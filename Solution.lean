/-
Licensed under the Apache License, Version 2.0. See LICENSE.
-/
module

public import Erdos684.Lower
public import Erdos684.Averaging
public import Erdos684.Analytic

/-!
# A verified quadratic-logarithmic upper bound for Erdős problem 684

The mathematical argument is adapted from APSSV26, Section 2. The explicit
constant here is weaker, allowing a Mathlib-only proof with Chebyshev estimates.
-/

@[expose] public section

open Filter Real Finset
open scoped Topology

namespace Erdos684

/-- The known quadratic-logarithmic bound, with the explicit nonoptimal constant `514`. -/
theorem upper_bound :
    ∀ᶠ n : ℕ in atTop, ∃ k ≤ n,
      (k : ℝ) ≤ 514 * (log (n : ℝ)) ^ 2 ∧ n ^ 2 < smallPrimePart n k := by
  filter_upwards [eventually_upper_parameters, eventually_averaging_gap] with n hn hgap
  obtain ⟨_, hn0, hXn, _, _, _, _, _, _, _, hXlog⟩ := hn
  have hfinite := averaged_smallPrimePart_lower n (primeCutoff n) (windowLength n) hn0 hXn
  have hex : ∃ k ∈ Finset.Icc 1 (2 * primeCutoff n), n ^ 2 < smallPrimePart n k := by
    by_contra h
    push_neg at h
    have hterm : ∀ k ∈ Finset.Icc 1 (2 * primeCutoff n),
        log (smallPrimePart n k : ℝ) ≤ 2 * log (n : ℝ) := by
      intro k hk
      have hu : smallPrimePart n k ≤ n ^ 2 := by
        have ht := h k hk
        omega
      have hr : (smallPrimePart n k : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hu
      have hl := Real.log_le_log (Nat.cast_pos.mpr (smallPrimePart_pos n k)) hr
      simpa only [Real.log_pow, Nat.cast_ofNat] using hl
    have hs := Finset.sum_le_sum hterm
    have hc : (∑ k ∈ Finset.Icc 1 (2 * primeCutoff n), 2 * log (n : ℝ)) =
        4 * (primeCutoff n : ℝ) * log n := by
      simp
      ring
    rw [hc] at hs
    linarith
  obtain ⟨k, hk, hku⟩ := hex
  have hkX := (Finset.mem_Icc.mp hk).2
  refine ⟨k, hkX.trans hXn, ?_, hku⟩
  have hkr : (k : ℝ) ≤ 2 * (primeCutoff n : ℝ) := by exact_mod_cast hkX
  exact hkr.trans hXlog

/-- There is an absolute quadratic-logarithmic bound on an index with large small-prime part. -/
theorem exists_upper_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∃ k ≤ n,
      (k : ℝ) ≤ C * (log (n : ℝ)) ^ 2 ∧ n ^ 2 < smallPrimePart n k := by
  exact ⟨514, by norm_num, upper_bound⟩

end Erdos684
