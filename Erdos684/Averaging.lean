/-
Licensed under the Apache License, Version 2.0. See LICENSE.
-/
module

public import Erdos684.Finite
public import Erdos684.BadPrimes
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# Finite averaging for the binomial small-prime threshold

This implements the prime-residue averaging strategy of APSSV26, Section 2,
using one full residue block and an adverse-residue cutoff.
-/

@[expose] public section

open Finset Real

namespace Erdos684

/-- Primes with more than `A` residues between the residue of `n` and the next multiple. -/
def goodPrimes (n X A : ℕ) : Finset ℕ :=
  (Nat.primesLE X).filter fun p => A < p - n % p

/-- Contribution of a prime to the logarithm of the small-prime part. -/
noncomputable def primeWeight (n k p : ℕ) : ℝ :=
  if p ≤ k then ((n.choose k).factorization p : ℝ) * log p else 0

lemma primeWeight_nonneg (n k p : ℕ) (hp : p.Prime) : 0 ≤ primeWeight n k p := by
  unfold primeWeight
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
  · exact le_rfl

lemma goodPrimeWeight_ge (n X A : ℕ) (hn : 0 < n) :
    Chebyshev.theta X - A * log (n + A : ℕ) ≤
      ∑ p ∈ goodPrimes n X A, log p := by
  classical
  have hsplit : (∑ p ∈ goodPrimes n X A, log (p : ℝ)) +
      (∑ p ∈ badPrimes n X A, log (p : ℝ)) = Chebyshev.theta X := by
    rw [goodPrimes, badPrimes, Chebyshev.theta_eq_sum_primesLE_log,
      Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : A < p - n % p
    · simp [h, not_le.mpr h]
    · simp [h, Nat.le_of_not_gt h]
  have hb := badPrimeWeight_le n X A hn
  linarith

lemma goodPrime_window_weight {n X A p : ℕ} (hX : 2 * X ≤ n)
    (hp : p ∈ goodPrimes n X A) :
    (A : ℝ) * log p ≤ ∑ k ∈ Finset.Icc 1 (2 * X), primeWeight n k p := by
  classical
  obtain ⟨hpX, hgap⟩ := Finset.mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primesLE hpX
  have hp_le := Nat.le_of_mem_primesLE hpX
  have hr := Nat.mod_lt n hprime.pos
  let g : ℕ → ℕ := fun i => p + n % p + i
  let T := (Finset.Icc 1 A).image g
  have hinj : Function.Injective g := by
    intro i j hij
    dsimp [g] at hij
    omega
  have hT : T ⊆ Finset.Icc 1 (2 * X) := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hi1, hiA⟩ := Finset.mem_Icc.mp hi
    dsimp [g]
    apply Finset.mem_Icc.mpr
    omega
  have hbound : ∀ k ∈ T, log (p : ℝ) ≤ primeWeight n k p := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hi1, hiA⟩ := Finset.mem_Icc.mp hi
    have hrem : n % p + i < p := by omega
    have hmod : n % p < g i % p := by
      dsimp [g]
      rw [Nat.add_assoc, Nat.add_mod_left, Nat.mod_eq_of_lt hrem]
      omega
    have hkn : g i ≤ n := (Finset.mem_Icc.mp (hT (Finset.mem_image.mpr ⟨i, by simp [hi1, hiA], rfl⟩))).2.trans hX
    have hfac := one_le_factorization_choose_of_mod_lt hprime hkn hmod
    have hpk : p ≤ g i := by dsimp [g]; omega
    rw [primeWeight, if_pos hpk]
    have hfacr : (1 : ℝ) ≤ (n.choose (g i)).factorization p := by exact_mod_cast hfac
    have hlp : 0 ≤ log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
    nlinarith [hlp]
  calc
    (A : ℝ) * log p = ∑ k ∈ T, log (p : ℝ) := by
      simp [T, Finset.card_image_of_injective _ hinj]
    _ ≤ ∑ k ∈ T, primeWeight n k p := Finset.sum_le_sum hbound
    _ ≤ ∑ k ∈ Finset.Icc 1 (2 * X), primeWeight n k p :=
      Finset.sum_le_sum_of_subset_of_nonneg hT fun k _ _ => primeWeight_nonneg n k p hprime

lemma goodPrime_sum_le_log (n X A k : ℕ) :
    ∑ p ∈ goodPrimes n X A, primeWeight n k p ≤ log (smallPrimePart n k : ℝ) := by
  classical
  rw [log_smallPrimePart]
  have heq : ∑ p ∈ goodPrimes n X A, primeWeight n k p =
      ∑ p ∈ (goodPrimes n X A).filter (fun p => p ≤ k),
        ((n.choose k).factorization p : ℝ) * log p := by
    simp [primeWeight, Finset.sum_filter]
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpg, hpk⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpk, Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hpg).1⟩
  · intro p hp _
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le))

/-- A finite lower bound on the average small-prime logarithm. -/
theorem averaged_smallPrimePart_lower (n X A : ℕ) (hn : 0 < n) (hX : 2 * X ≤ n) :
    (A : ℝ) * (Chebyshev.theta X - A * log (n + A : ℕ)) ≤
      ∑ k ∈ Finset.Icc 1 (2 * X), log (smallPrimePart n k : ℝ) := by
  calc
    (A : ℝ) * (Chebyshev.theta X - A * log (n + A : ℕ)) ≤
        A * ∑ p ∈ goodPrimes n X A, log (p : ℝ) :=
      mul_le_mul_of_nonneg_left (goodPrimeWeight_ge n X A hn) (Nat.cast_nonneg A)
    _ = ∑ p ∈ goodPrimes n X A, (A : ℝ) * log p := by rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ goodPrimes n X A, ∑ k ∈ Finset.Icc 1 (2 * X), primeWeight n k p :=
      Finset.sum_le_sum fun p hp => goodPrime_window_weight hX hp
    _ = ∑ k ∈ Finset.Icc 1 (2 * X), ∑ p ∈ goodPrimes n X A, primeWeight n k p := Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.Icc 1 (2 * X), log (smallPrimePart n k : ℝ) :=
      Finset.sum_le_sum fun k _ => goodPrime_sum_le_log n X A k

end Erdos684
