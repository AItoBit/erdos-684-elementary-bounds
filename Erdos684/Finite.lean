/-
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Finite arithmetic for Erdős problem 684

The small-prime part includes the full multiplicity of each prime at most the
lower binomial index. The finite obstruction is the no-carry construction in
Alexeev, Putterman, Sawhney, Sellke and Valiant, Theorem 2.1:
https://arxiv.org/html/2603.29961v2#S2.
-/

@[expose] public section

namespace Erdos684

/-- The factor of `n.choose k` supported on primes at most `k`. -/
def smallPrimePart (n k : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesLE k, p ^ ((n.choose k).factorization p)

theorem smallPrimePart_pos (n k : ℕ) : 0 < smallPrimePart n k := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primesLE hp).pos _

/-- The logarithm is the weighted sum of small-prime valuations. -/
theorem log_smallPrimePart (n k : ℕ) :
    Real.log (smallPrimePart n k : ℝ) =
      ∑ p ∈ Nat.primesLE k, ((n.choose k).factorization p : ℝ) * Real.log p := by
  rw [smallPrimePart, Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p _
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    exact_mod_cast pow_ne_zero ((n.choose k).factorization p) (Nat.prime_of_mem_primesLE hp).ne_zero

/-- A first-level carry forces a positive prime exponent in the binomial coefficient. -/
theorem factorization_choose_pos_of_mod_lt {n k p : ℕ} (hp : p.Prime)
    (hkn : k ≤ n) (hmod : n % p < k % p) :
    0 < (n.choose k).factorization p := by
  have hsum := Nat.add_mod k (n - k) p
  rw [Nat.add_sub_of_le hkn] at hsum
  have hkmod := Nat.mod_lt k hp.pos
  have hnmod := Nat.mod_lt (n - k) hp.pos
  have hcarry : p ≤ k % p + (n - k) % p := by
    by_contra h
    have hlt : k % p + (n - k) % p < p := by omega
    rw [Nat.mod_eq_of_lt hlt] at hsum
    omega
  rw [Nat.factorization_choose hp hkn (b := Nat.log p n + 2) (by omega)]
  apply Finset.card_pos.mpr
  refine ⟨1, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_Ico, pow_one]
  exact ⟨⟨by omega, by omega⟩, hcarry⟩

theorem one_le_factorization_choose_of_mod_lt {n k p : ℕ} (hp : p.Prime)
    (hkn : k ≤ n) (hmod : n % p < k % p) :
    1 ≤ (n.choose k).factorization p :=
  factorization_choose_pos_of_mod_lt hp hkn hmod

theorem dvd_choose_of_mod_lt {n k p : ℕ} (hp : p.Prime)
    (hkn : k ≤ n) (hmod : n % p < k % p) : p ∣ n.choose k :=
  Nat.dvd_of_factorization_pos (Nat.ne_of_gt (factorization_choose_pos_of_mod_lt hp hkn hmod))

/-- Multiplying primes with a first-level carry gives a lower bound on the small-prime part. -/
theorem carry_prime_product_le (n k : ℕ) (hkn : k ≤ n) :
    (∏ p ∈ (Nat.primesLE k).filter (fun p => n % p < k % p), p) ≤
      smallPrimePart n k := by
  let s := (Nat.primesLE k).filter (fun p => n % p < k % p)
  calc
    (∏ p ∈ s, p) ≤ ∏ p ∈ s, p ^ ((n.choose k).factorization p) := by
      apply Finset.prod_le_prod'
      intro p hp
      obtain ⟨hpk, hmod⟩ := Finset.mem_filter.mp hp
      exact Nat.le_self_pow (Nat.ne_of_gt
        (factorization_choose_pos_of_mod_lt (Nat.prime_of_mem_primesLE hpk) hkn hmod)) p
    _ ≤ smallPrimePart n k := by
      apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
      intro p hp _
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.prime_of_mem_primesLE hp).ne_zero)

/-- The predecessor of a positive multiple has the largest possible residue. -/
theorem pred_mod_of_dvd {M q : ℕ} (hM : 0 < M) (_hq : 0 < q) (hdiv : q ∣ M) :
    (M - 1) % q = q - 1 := by
  obtain ⟨t, rfl⟩ := hdiv
  simpa using Nat.mul_sub_mod (n := q) (p := t) (x := 0) hM

/-- A sufficiently large prime power divisor prevents all carries for a small lower index. -/
theorem pred_mod_prime_pow_ge {M K p e : ℕ} (hM : 0 < M) (hp : p.Prime)
    (hlarge : K < p ^ e) (hdiv : p ^ e ∣ M) {k : ℕ} (hk : k ≤ K) (i : ℕ) :
    k % p ^ i ≤ (M - 1) % p ^ i := by
  have hpow : 0 < p ^ i := pow_pos hp.pos _
  by_cases hi : i ≤ e
  · have hd : p ^ i ∣ M := (Nat.pow_dvd_pow p hi).trans hdiv
    rw [pred_mod_of_dvd hM hpow hd]
    have hmod := Nat.mod_lt k hpow
    omega
  · have hd : p ^ e ∣ p ^ i := Nat.pow_dvd_pow p (by omega)
    have hmod := Nat.mod_mod_of_dvd (M - 1) hd
    have hle := Nat.mod_le ((M - 1) % p ^ i) (p ^ e)
    rw [hmod, pred_mod_of_dvd hM (pow_pos hp.pos _) hdiv] at hle
    have hkmod := Nat.mod_le k (p ^ i)
    omega

/-- A residue inequality excludes a carry when a natural number is split into two summands. -/
theorem no_carry_of_mod_le {n k q : ℕ} (hkn : k ≤ n) (hq : 0 < q)
    (hmod : k % q ≤ n % q) : k % q + (n - k) % q < q := by
  have ha := Nat.mod_lt k hq
  have hb := Nat.mod_lt (n - k) hq
  have hsum := Nat.add_mod k (n - k) q
  rw [Nat.add_sub_of_le hkn] at hsum
  by_contra h
  have hle : q ≤ k % q + (n - k) % q := by omega
  have hlt : k % q + (n - k) % q - q < q := by omega
  rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hlt] at hsum
  omega

/-- A prime power divisor exceeding the lower index forces zero binomial valuation. -/
theorem factorization_choose_pred_eq_zero {M K p e : ℕ} (hM : 0 < M) (hp : p.Prime)
    (hlarge : K < p ^ e) (hdiv : p ^ e ∣ M) {k : ℕ} (hk : k ≤ K) :
    ((M - 1).choose k).factorization p = 0 := by
  by_cases hkn : k ≤ M - 1
  · rw [Nat.factorization_choose hp hkn (b := Nat.log p (M - 1) + 1) (by omega)]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    exact not_le.mpr (no_carry_of_mod_le hkn (pow_pos hp.pos _)
      (pred_mod_prime_pow_ge hM hp hlarge hdiv hk i))
  · rw [Nat.choose_eq_zero_of_lt (by omega : M - 1 < k)]
    simp

/-- If each small prime has a divisor power exceeding `K`, every small-prime part up to `K` is one. -/
theorem smallPrimePart_pred_eq_one {M K : ℕ} (hM : 0 < M)
    (hpowers : ∀ p, p.Prime → p ≤ K → ∃ e, K < p ^ e ∧ p ^ e ∣ M)
    {k : ℕ} (hk : k ≤ K) : smallPrimePart (M - 1) k = 1 := by
  apply Finset.prod_eq_one
  intro p hp
  obtain ⟨hpk, hprime⟩ := Nat.mem_primesLE.mp hp
  obtain ⟨e, hlarge, hdiv⟩ := hpowers p hprime (by omega)
  rw [factorization_choose_pred_eq_zero hM hprime hlarge hdiv hk, pow_zero]

end Erdos684
