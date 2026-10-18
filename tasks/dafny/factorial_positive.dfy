function Factorial(n: nat): nat
  decreases n
{
  if n == 0 then 1 else n * Factorial(n - 1)
}

lemma FactorialPositive(n: nat)
  ensures Factorial(n) > 0
  decreases n
{
  {{CANDIDATE}}
}

lemma RequiredGoal(n: nat)
  ensures Factorial(n) > 0
{
  FactorialPositive(n);
}

