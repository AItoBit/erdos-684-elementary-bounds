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

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega

/-!
# Elementary analytic bounds for an upper bound in Erdős problem 684

The estimates use Chebyshev's elementary lower bound for the prime-weighted sum.
No prime number theorem hypothesis is used. The averaging strategy follows
Alexeev, Putterman, Sawhney, Sellke and Valiant, Theorem 2.1:
https://arxiv.org/html/2603.29961v2#S2.
-/

open Filter Real
open scoped Topology

@[expose] public section

namespace Erdos684

noncomputable def primeCutoff (n : ℕ) : ℕ := Nat.ceil (256 * (log (n : ℝ)) ^ 2)

noncomputable def windowLength (n : ℕ) : ℕ := Nat.ceil (32 * log (n : ℝ))

lemma log_add_div_tendsto_zero (b : ℝ) :
    Tendsto (fun x : ℝ => log (x + b) / x) atTop (𝓝 0) := by
  have h := (Real.tendsto_log_comp_add_sub_log b).div_atTop tendsto_id
  have h' := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  convert h.add h' using 1 <;> simp only [id_eq, add_zero]
  ext x
  ring

lemma sqrt_mul_log_div_tendsto_zero :
    Tendsto (fun x : ℝ => 2 * sqrt x * log x / x) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => log x / sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  have he : (fun x : ℝ => 2 * sqrt x * log x / x) =ᶠ[atTop]
      (fun x => 2 * (log x / sqrt x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hs : sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
    have heq := congrArg (fun z : ℝ => z * log x) (Real.mul_self_sqrt hx.le)
    field_simp [hx.ne', hs]
    nlinarith
  simpa using (h.const_mul 2).congr' he.symm

/-- A weak eventual lower bound for the prime-weighted sum follows from Chebyshev. -/
lemma eventually_theta_ge_half :
    ∀ᶠ x : ℝ in atTop, x / 2 ≤ Chebyshev.theta x := by
  have hconst : Tendsto (fun x : ℝ => log 2 / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have herr : Tendsto (fun x : ℝ => log 2 / x + log (x + 2) / x +
      2 * sqrt x * log x / x) atTop (𝓝 0) := by
    simpa only [add_zero] using
      (hconst.add (log_add_div_tendsto_zero 2)).add sqrt_mul_log_div_tendsto_zero
  have hlogtwo : (1 / 2 : ℝ) < log 2 := by
    have h := Real.lt_log_one_add_of_pos (x := 1) (by norm_num)
    norm_num at h
    linarith
  have hsmall := herr.eventually_lt_const (by linarith : (0 : ℝ) < log 2 - 1 / 2)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hratio : (log 2 + log (x + 2) + 2 * sqrt x * log x) / x < log 2 - 1 / 2 := by
    simpa only [add_div] using hx
  have hb := (div_lt_iff₀ hx0).mp hratio
  have ht := Chebyshev.theta_ge' hx1
  nlinarith

lemma primeCutoff_tendsto :
    Tendsto (fun n : ℕ => (primeCutoff n : ℝ)) atTop atTop := by
  have hL : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun n : ℕ => 256 * (log (n : ℝ)) ^ 2) atTop atTop := by
    simpa only [pow_two] using
      (hL.atTop_mul_atTop₀ hL).const_mul_atTop (by norm_num : (0 : ℝ) < 256)
  exact tendsto_atTop_mono (fun n => Nat.le_ceil _) hbase

/-- Bounds for the two rounded parameters used by the finite averaging argument. -/
lemma eventually_upper_parameters :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ log (n : ℝ) ∧
      0 < n ∧
      2 * primeCutoff n ≤ n ∧
      windowLength n ≤ n ∧
      32 * log (n : ℝ) ≤ (windowLength n : ℝ) ∧
      (windowLength n : ℝ) ≤ 33 * log (n : ℝ) ∧
      256 * (log (n : ℝ)) ^ 2 ≤ (primeCutoff n : ℝ) ∧
      (primeCutoff n : ℝ) ≤ 257 * (log (n : ℝ)) ^ 2 ∧
      log ((n + windowLength n : ℕ) : ℝ) ≤ 2 * log (n : ℝ) ∧
      (primeCutoff n : ℝ) / 2 ≤ Chebyshev.theta (primeCutoff n) ∧
      (2 * primeCutoff n : ℝ) ≤ 514 * (log (n : ℝ)) ^ 2 := by
  have hL : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => (log (n : ℝ)) ^ 2 / n) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hxr : Tendsto (fun n : ℕ => 2 * (256 * (log (n : ℝ)) ^ 2 + 1) / n)
      atTop (𝓝 0) := by
    convert ((hratio.const_mul 512).add (hone.const_mul 2)) using 1 <;> try norm_num
    ext n
    ring
  have hlr : Tendsto (fun n : ℕ => log (n : ℝ) / n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have har : Tendsto (fun n : ℕ => 33 * log (n : ℝ) / n) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using hlr.const_mul 33
  have hxsmall := hxr.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  have hasmall := har.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  have htheta := primeCutoff_tendsto.eventually eventually_theta_ge_half
  filter_upwards [hL.eventually_ge_atTop 1, eventually_gt_atTop (0 : ℕ),
    hxsmall, hasmall, htheta] with n hL1 hn0 hxs has ht
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hL0 : 0 ≤ log (n : ℝ) := by linarith
  have hLsq : 1 ≤ (log (n : ℝ)) ^ 2 := by nlinarith
  have hAlower : 32 * log (n : ℝ) ≤ (windowLength n : ℝ) := Nat.le_ceil _
  have hAceil : (windowLength n : ℝ) < 32 * log (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hAupper : (windowLength n : ℝ) ≤ 33 * log (n : ℝ) := by linarith
  have hXlower : 256 * (log (n : ℝ)) ^ 2 ≤ (primeCutoff n : ℝ) := Nat.le_ceil _
  have hXceil : (primeCutoff n : ℝ) < 256 * (log (n : ℝ)) ^ 2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hXupper : (primeCutoff n : ℝ) ≤ 257 * (log (n : ℝ)) ^ 2 := by linarith
  have hxlarge := (div_lt_iff₀ hnpos).mp hxs
  have halarge := (div_lt_iff₀ hnpos).mp has
  have h2X : 2 * primeCutoff n ≤ n := by
    have h : (2 : ℝ) * primeCutoff n ≤ n := by linarith
    exact_mod_cast h
  have hAn : windowLength n ≤ n := by
    have h : (windowLength n : ℝ) ≤ n := by linarith
    exact_mod_cast h
  have hsumpos : (0 : ℝ) < ((n + windowLength n : ℕ) : ℝ) := by positivity
  have hsum : ((n + windowLength n : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast (by omega : n + windowLength n ≤ 2 * n)
  have hlogsum := Real.log_le_log hsumpos hsum
  rw [Real.log_mul (by norm_num) hnpos.ne'] at hlogsum
  have hlogtwo := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
  have hlogbound : log ((n + windowLength n : ℕ) : ℝ) ≤ 2 * log (n : ℝ) := by linarith
  refine ⟨hL1, hn0, h2X, hAn, hAlower, hAupper, hXlower, hXupper, hlogbound, ht, ?_⟩
  nlinarith

/-- The explicit constants leave a positive margin in the finite averaging inequality. -/
lemma eventually_averaging_gap :
    ∀ᶠ n : ℕ in atTop,
      4 * (primeCutoff n : ℝ) * log n <
        (windowLength n : ℝ) * (Chebyshev.theta (primeCutoff n) -
          (windowLength n : ℝ) * log ((n + windowLength n : ℕ) : ℝ)) := by
  filter_upwards [eventually_upper_parameters] with n hn
  obtain ⟨hL, _, _, _, ha, hau, hx, hxu, hb, ht, _⟩ := hn
  have hL0 : 0 ≤ log (n : ℝ) := by linarith
  have ha0 : (0 : ℝ) ≤ windowLength n := Nat.cast_nonneg _
  have hab := mul_le_mul_of_nonneg_left hb ha0
  have hab' := mul_le_mul_of_nonneg_right hau (show 0 ≤ 2 * log (n : ℝ) by positivity)
  have hbudget : 62 * (log (n : ℝ)) ^ 2 ≤
      Chebyshev.theta (primeCutoff n) -
        (windowLength n : ℝ) * log ((n + windowLength n : ℕ) : ℝ) := by
    nlinarith
  have hprod := mul_le_mul ha hbudget (by positivity) ha0
  have hXprod := mul_le_mul_of_nonneg_right hxu (show 0 ≤ 4 * log (n : ℝ) by positivity)
  have hcube : 0 < (log (n : ℝ)) ^ 3 := pow_pos (by linarith) _
  nlinarith

end Erdos684
