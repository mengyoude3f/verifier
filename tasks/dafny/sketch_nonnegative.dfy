// Fixed harness for the Sketch demonstration task. The model may only supply
// helper lemma declarations and their proof bodies at the marked insertion.
{{SKETCH}}

lemma RequiredGoal(n: nat)
  ensures n >= 0
{
  MainProof(n);
}
