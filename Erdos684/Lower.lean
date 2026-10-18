/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Erdos684.Finite
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# A coarse logarithmic lower bound for Erdős problem 684

The prime-power obstruction follows Alexeev, Putterman, Sawhney, Sellke and
Valiant, Theorem 2.1, https://arxiv.org/html/2603.29961v2#S2.
Chebyshev's elementary upper bounds give the weaker coefficient $1/8$ here.
This file does not claim the source's sharper coefficient $1/2$.
-/

@[expose] public section

open Filter Real
open scoped Topology

namespace Erdos684

/-- The modulus contains a prime power larger than `K` for every prime at most `K`. -/
def obstructionModulus (K : ℕ) : ℕ := Nat.lcmUpto K * primorial K

lemma obstructionModulus_pos (K : ℕ) : 0 < obstructionModulus K :=
  Nat.mul_pos (Nat.lcmUpto_pos K) (primorial_pos K)

lemma prime_power_dvd_obstructionModulus {K p : ℕ} (hp : p.Prime) (hpk : p ≤ K) :
    p ^ (Nat.log p K + 1) ∣ obstructionModulus K := by
  have hd : p ^ Nat.log p K ∣ Nat.lcmUpto K :=
    (hp.pow_dvd_iff_le_factorization (Nat.lcmUpto_ne_zero K)).mpr (by
      rw [Nat.factorization_lcmUpto K hp])
  have hpdiv : p ∣ primorial K := hp.dvd_primorial_iff.mpr hpk
  simpa only [obstructionModulus, pow_succ] using mul_dvd_mul hd hpdiv

lemma smallPrimePart_obstruction_eq_one (K : ℕ) {k : ℕ} (hk : k ≤ K) :
    smallPrimePart (obstructionModulus K - 1) k = 1 := by
  apply smallPrimePart_pred_eq_one (obstructionModulus_pos K) _ hk
  intro p hp hpk
  refine ⟨Nat.log p K + 1, ?_, prime_power_dvd_obstructionModulus hp hpk⟩
  exact Nat.lt_pow_succ_log_self hp.one_lt K

lemma lt_obstructionModulus {K : ℕ} (hK : 2 < K) : K < obstructionModulus K := by
  apply (lt_primorial_self hK).trans_le
  exact Nat.le_mul_of_pos_left (primorial K) (Nat.lcmUpto_pos K)

/-- Chebyshev's explicit estimates suffice to bound the logarithm of the obstruction modulus. -/
lemma log_obstructionModulus_le (K : ℕ) : log (obstructionModulus K : ℝ) ≤ 8 * K := by
  have hpsi := Chebyshev.psi_le_const_mul_self (x := (K : ℝ)) (Nat.cast_nonneg K)
  have htheta := Chebyshev.theta_le_log4_mul_x (x := (K : ℝ)) (Nat.cast_nonneg K)
  have hthetaeq : Chebyshev.theta (K : ℝ) = log (primorial K : ℝ) := by
    simpa using Chebyshev.theta_eq_log_primorial (K : ℝ)
  have hpsieq := Chebyshev.psi_eq_log_lcmUpto K
  have hlog4 : log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  rw [obstructionModulus, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr (Nat.lcmUpto_ne_zero K))
      (Nat.cast_ne_zero.mpr (primorial_ne_zero K))]
  rw [← hthetaeq, ← hpsieq]
  nlinarith [Nat.cast_nonneg (α := ℝ) K]

/-- Infinitely many inputs have small-prime part one throughout a logarithmic window. -/
theorem frequently_smallPrimePart_eq_one :
    ∃ᶠ n : ℕ in atTop, 1 < n ∧
      ∀ k : ℕ, (k : ℝ) ≤ log (n : ℝ) / 8 → smallPrimePart n k = 1 := by
  apply frequently_atTop'.mpr
  intro N
  let K := max (N + 1) 3
  have hK : 2 < K := by dsimp [K]; omega
  have hNK : N < K := by dsimp [K]; omega
  have hmod := lt_obstructionModulus hK
  let n := obstructionModulus K - 1
  have hKn : K ≤ n := by dsimp [n]; omega
  have hn : 1 < n := by omega
  refine ⟨n, hNK.trans_le hKn, hn, ?_⟩
  intro k hk
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hlog : log (n : ℝ) ≤ log (obstructionModulus K : ℝ) := by
    apply Real.log_le_log hnpos
    exact_mod_cast (show n ≤ obstructionModulus K by dsimp [n]; omega)
  have hbound := log_obstructionModulus_le K
  have hkK : k ≤ K := by
    have : (k : ℝ) ≤ K := by linarith
    exact_mod_cast this
  exact smallPrimePart_obstruction_eq_one K hkK

end Erdos684
