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

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Lean.Elab.Tactic.Omega

/-!
# A finite bound on adverse prime residues

The primes for which `p - n % p` is small divide a short product after `n`.
This is the finite counting observation in Section 2 of Alexeev, Putterman,
Sawhney, Sellke and Valiant, *Short proofs in combinatorics and number theory*:
https://arxiv.org/html/2603.29961v2#S2.
-/

@[expose] public section

namespace Erdos684

/-- Primes up to `X` whose residue gap after `n` is at most `A`. -/
def badPrimes (n X A : ℕ) : Finset ℕ :=
  (Nat.primesLE X).filter fun p => p - n % p ≤ A

/-- A positive modulus divides the integer reached at its next residue gap. -/
theorem dvd_add_residue_gap (n p : ℕ) (hp : 0 < p) :
    p ∣ n + (p - n % p) := by
  have hr := Nat.mod_lt n hp
  have hdecomp := Nat.mod_add_div n p
  refine ⟨n / p + 1, ?_⟩
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- Each adverse prime divides the product of the next `A` positive terms. -/
theorem badPrime_dvd_intervalProduct {n X A p : ℕ}
    (hp : p ∈ badPrimes n X A) :
    p ∣ ∏ j ∈ Finset.Icc 1 A, (n + j) := by
  obtain ⟨hpX, hgap⟩ := Finset.mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primesLE hpX
  have hpos : 1 ≤ p - n % p := by
    have hr := Nat.mod_lt n hprime.pos
    omega
  exact (dvd_add_residue_gap n p hprime.pos).trans
    (Finset.dvd_prod_of_mem (fun j => n + j) (Finset.mem_Icc.mpr ⟨hpos, hgap⟩))

/-- The logarithmic weight of adverse primes is bounded by a short product.
The assertion includes `A = 0`, when the prime set is empty. -/
theorem badPrimeWeight_le (n X A : ℕ) (hn : 0 < n) :
    ∑ p ∈ badPrimes n X A, Real.log (p : ℝ) ≤
      (A : ℝ) * Real.log (n + A : ℕ) := by
  let B := badPrimes n X A
  let P : ℕ := ∏ p ∈ B, p
  let Q : ℕ := ∏ j ∈ Finset.Icc 1 A, (n + j)
  have hQpos : 0 < Q := by
    exact Finset.prod_pos fun j _ => Nat.add_pos_left hn j
  have hPpos : 0 < P := by
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).pos
  have hsubset : B ⊆ Q.primeFactors := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
    exact hprime.mem_primeFactors (badPrime_dvd_intervalProduct hp) hQpos.ne'
  have hdiv : P ∣ Q :=
    (Finset.prod_dvd_prod_of_subset B Q.primeFactors (fun p => p) hsubset).trans
      (Nat.prod_primeFactors_dvd Q)
  have hPQ : P ≤ Q := Nat.le_of_dvd hQpos hdiv
  have hlogP : Real.log (P : ℝ) = ∑ p ∈ B, Real.log (p : ℝ) := by
    dsimp [P]
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).ne_zero
  have hlogQ : Real.log (Q : ℝ) =
      ∑ j ∈ Finset.Icc 1 A, Real.log (n + j : ℕ) := by
    dsimp [Q]
    rw [Nat.cast_prod, Real.log_prod]
    intro j _
    exact_mod_cast (Nat.add_pos_left hn j).ne'
  calc
    ∑ p ∈ badPrimes n X A, Real.log (p : ℝ) = Real.log (P : ℝ) := hlogP.symm
    _ ≤ Real.log (Q : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr hPpos) (Nat.cast_le.mpr hPQ)
    _ = ∑ j ∈ Finset.Icc 1 A, Real.log (n + j : ℕ) := hlogQ
    _ ≤ ∑ _j ∈ Finset.Icc 1 A, Real.log (n + A : ℕ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Real.log_le_log (Nat.cast_pos.mpr (Nat.add_pos_left hn j))
      exact Nat.cast_le.mpr (Nat.add_le_add_left (Finset.mem_Icc.mp hj).2 n)
    _ = (A : ℝ) * Real.log (n + A : ℕ) := by simp

end Erdos684
