"""Minimal client for GLM's Anthropic-compatible Messages API."""
#把提示词发送给 GLM，并把模型返回的文本交给上层代码

from __future__ import annotations

import os
import re
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import requests


class GLMClientError(RuntimeError):
    """A safe-to-print API error that never includes credentials."""
#项目自定义的异常类型。调用失败时统一抛出它，上层 runner.py 会把它转换成 API_ERROR。

@dataclass(frozen=True)#不可修改，全部支持环境变量
class GLMConfig:
    api_key: str
    base_url: str = "https://api-gateway.glm.ai"
    model: str = "glm-5.3-highspeed"
    max_tokens: int = 4096#最大输出
    timeout_seconds: float = 180.0#单次超时(ms)
    max_retries: int = 3
    retry_delay_seconds: float = 1.0

    @classmethod
    def load(cls, project_dir: Path | None = None) -> "GLMConfig":#读取 api_key：环境变量 -> api_key.md -> 报错
        root = project_dir or Path(__file__).resolve().parent
        api_key = os.environ.get("GLM_API_KEY", "").strip()
        if not api_key:
            key_file = Path(os.environ.get("GLM_API_KEY_FILE", root / "api_key.md"))
            if key_file.is_file():
                api_key = _parse_key_file(key_file)
        if not api_key:
            raise GLMClientError(
                "GLM API key is missing; set GLM_API_KEY or create api_key.md"
            )

        return cls(
            api_key=api_key,
            base_url=os.environ.get(
                "GLM_BASE_URL", "https://api-gateway.glm.ai"
            ).rstrip("/"),
            model=os.environ.get("GLM_MODEL", "glm-5.3-highspeed"),
            max_tokens=_positive_int_env("GLM_MAX_TOKENS", 4096),
            timeout_seconds=float(os.environ.get("GLM_TIMEOUT_SECONDS", "180")),
            max_retries=_positive_int_env("GLM_MAX_RETRIES", 3),
            retry_delay_seconds=float(os.environ.get("GLM_RETRY_DELAY_SECONDS", "1")),
        )


def _parse_key_file(path: Path) -> str:#解析不同格式中的 api_key
    value = path.read_text(encoding="utf-8").strip()
    bearer_match = re.search(
        r"Authorization\s*:\s*Bearer\s+([^\s\"']+)", value, flags=re.I
    )
    if bearer_match:
        value = bearer_match.group(1)
    if value.startswith("```") and value.endswith("```"):
        value = value[3:-3].strip()
    if "=" in value and "\n" not in value:
        name, candidate = value.split("=", 1)
        if name.strip() in {"GLM_API_KEY", "ANTHROPIC_AUTH_TOKEN"}:
            value = candidate.strip().strip('"').strip("'")
    if value.lower().startswith("bearer "):
        value = value[7:].strip()
    if not value or any(ch.isspace() for ch in value):
        raise GLMClientError("api_key.md does not contain one valid API key")
    return value


def _positive_int_env(name: str, default: int) -> int:#读取必须为正整数的环境变量
    value = int(os.environ.get(name, str(default)))
    if value <= 0:
        raise GLMClientError(f"{name} must be positive")
    return value


class GLMClient:
    def __init__(self, config: GLMConfig | None = None):
        self.config = config or GLMConfig.load()
        self._session = requests.Session()

    def generate(self, prompt: str, *, max_tokens: int | None = None) -> str:#发起请求：拒绝空提示词，请求体采用 Anthropic Messages 格式
        if not prompt.strip():
            raise GLMClientError("prompt must not be empty")

        endpoint = f"{self.config.base_url}/v1/messages"
        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {self.config.api_key}",
            "anthropic-version": "2023-06-01",
        }
        payload = {
            "model": self.config.model,
            "max_tokens": max_tokens or self.config.max_tokens,
            "messages": [{"role": "user", "content": prompt}],
        }

        last_error = "GLM API request failed"
        for attempt in range(1, self.config.max_retries + 1):#超时/网络连接错误/HTTP XXX/返回异常 重试
            try:
                response = self._session.post(
                    endpoint,
                    headers=headers,
                    json=payload,
                    timeout=self.config.timeout_seconds,
                )
            except requests.Timeout:
                last_error = "GLM API request timed out"
                if attempt < self.config.max_retries:
                    _sleep_before_retry(self.config.retry_delay_seconds)
                    continue
                raise GLMClientError(
                    f"{last_error} after {attempt} attempts"
                )
            except requests.RequestException as exc:
                last_error = f"GLM API request failed: {type(exc).__name__}"
                if attempt < self.config.max_retries:
                    _sleep_before_retry(self.config.retry_delay_seconds)
                    continue
                raise GLMClientError(
                    f"{last_error} after {attempt} attempts"
                )

            if response.status_code in {408, 425, 429} or response.status_code >= 500:
                last_error = (
                    f"GLM API returned HTTP {response.status_code}: "
                    f"{_safe_error_message(response)}"
                )
                if attempt < self.config.max_retries:
                    _sleep_before_retry(self.config.retry_delay_seconds)
                    continue
                raise GLMClientError(f"{last_error} after {attempt} attempts")

            if not response.ok:
                message = _safe_error_message(response)
                raise GLMClientError(
                    f"GLM API returned HTTP {response.status_code}: {message}"
                )

            try:
                data = response.json()
            except ValueError:
                last_error = "GLM API returned non-JSON content"
                if attempt < self.config.max_retries:
                    _sleep_before_retry(self.config.retry_delay_seconds)
                    continue
                raise GLMClientError(f"{last_error} after {attempt} attempts")

            if not isinstance(data, dict):
                last_error = "GLM API returned an invalid JSON object"
                if attempt < self.config.max_retries:
                    _sleep_before_retry(self.config.retry_delay_seconds)
                    continue
                raise GLMClientError(f"{last_error} after {attempt} attempts")

            text = _extract_anthropic_text(data)
            if text.strip():
                return text
            last_error = "GLM API returned no text content"
            if attempt < self.config.max_retries:
                _sleep_before_retry(self.config.retry_delay_seconds)
                continue
            raise GLMClientError(f"{last_error} after {attempt} attempts")

        raise GLMClientError(last_error)


def _extract_anthropic_text(data: dict[str, Any]) -> str:#请求成功后只提取文本
    content = data.get("content")
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        chunks = [
            block.get("text", "")
            for block in content
            if isinstance(block, dict) and block.get("type") == "text"
        ]
        return "".join(chunks)
    return ""


def _safe_error_message(response: requests.Response) -> str:#提取简明化报错
    try:
        data = response.json()
        if isinstance(data, dict):
            error = data.get("error", data)
            if isinstance(error, dict):
                return str(error.get("message", error.get("type", "request rejected")))[:500]
            return str(error)[:500]
        return str(data)[:500]
    except ValueError:
        return (response.text or "request rejected")[:500]


def _sleep_before_retry(delay_seconds: float) -> None:
    time.sleep(max(0.0, delay_seconds))

#finish review：2026.9.14