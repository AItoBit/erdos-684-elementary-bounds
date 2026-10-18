/-
Licensed under the Apache License, Version 2.0. See LICENSE.
-/
module

public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Challenge: known elementary bounds in Erdős problem 684

The two holes are deliberate statement-comparison challenges. Solution.lean
provides the independently implemented proof. The optimal order remains open.
-/

@[expose] public section

set_option warn.sorry false

open Filter Real

namespace Erdos684

/-- Full prime-power part of the binomial coefficient supported on primes at most `k`. -/
def smallPrimePart (n k : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesLE k, p ^ ((n.choose k).factorization p)

/-- A quadratic-logarithmic upper bound, with a nonoptimal explicit constant. -/
theorem upper_bound :
    ∀ᶠ n : ℕ in atTop, ∃ k ≤ n,
      (k : ℝ) ≤ 514 * (log (n : ℝ)) ^ 2 ∧ n ^ 2 < smallPrimePart n k := by
  sorry

/-- Infinitely many inputs have no small-prime factors throughout a logarithmic window. -/
theorem frequently_smallPrimePart_eq_one :
    ∃ᶠ n : ℕ in atTop, 1 < n ∧
      ∀ k : ℕ, (k : ℝ) ≤ log (n : ℝ) / 8 → smallPrimePart n k = 1 := by
  sorry

end Erdos684
