// Fixed harness for the nested Sketch task. The model may only supply lemma
// declarations and their proof bodies at the marked insertion; it may also
// decompose a hole into further lemmas, which land at the same insertion.
function Sum(n: nat): nat
  decreases n
{
  if n == 0 then 0 else n + Sum(n - 1)
}

{{SKETCH}}

lemma RequiredGoal(n: nat)
  ensures Sum(n) * 2 == n * (n + 1)
{
  MainProof(n);
}
