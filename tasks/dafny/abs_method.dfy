method Abs(x: int) returns (y: int)
  ensures y >= 0
  ensures y == x || y == -x
{
  {{CANDIDATE}}
}

