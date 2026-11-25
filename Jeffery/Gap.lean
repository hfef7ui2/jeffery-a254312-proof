import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Jeffery

/-- The statement of Logs23.lam_lower. Parameter order and casts are identical. -/
def LargeLogBound : Prop :=
  ∀ k l : ℕ, 20000 < k →
    1 / ((2 : ℝ)^k-1) ≤ |((k+l : ℕ) : ℝ)*Real.log 2 - (k : ℝ)*Real.log 3|

def GapAt (v : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → 3^v < 2^(n+v) → 3^v + 2^n ≤ 2^(n+v) + 1

set_option maxRecDepth 10000 in
private theorem finite_gaps : ∀ i j : Fin 35,
    i.val + j.val ≤ 34 → 0 < i.val → 0 < j.val → 3^j.val < 2^(i.val+j.val) →
      3^j.val + 2^i.val ≤ 2^(i.val+j.val) + 1 := by decide

theorem gap_small {n v : ℕ} (hn : 0 < n) (hv : 0 < v) (hx : n+v ≤ 27)
    (h : 3^v < 2^(n+v)) : 3^v + 2^n ≤ 2^(n+v)+1 :=
  finite_gaps ⟨n, by omega⟩ ⟨v, by omega⟩ (by change n+v ≤ 34; omega) hn hv h

private theorem gap_when_n_gt_v {n v : ℕ} (hv : 0 < v) (hnv : v < n) :
    3^v + 2^n ≤ 2^(n+v)+1 := by
  have ha : 3^v ≤ 2^v*2^v := by
    calc
      3^v ≤ 4^v := Nat.pow_le_pow_left (by decide) _
      _ = 2^v*2^v := by rw [← mul_pow]; norm_num
  have hb : 2*2^v ≤ 2^n := by
    rw [← Nat.pow_succ']
    exact Nat.pow_le_pow_right (by decide) hnv
  have hc : 2 ≤ 2^v := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) hv : 2^1 ≤ 2^v)
  have hfirst : 2*3^v ≤ 2^n*2^v := by nlinarith [Nat.mul_le_mul_right (2^v) hb]
  have hsecond : 2*2^n ≤ 2^n*2^v := by nlinarith [Nat.mul_le_mul_left (2^n) hc]
  rw [pow_add]
  omega

private theorem positive_log_gap {n v : ℕ} (h : 3^v < 2^(n+v)) :
    0 < ((v+n : ℕ) : ℝ)*Real.log 2 - (v : ℝ)*Real.log 3 := by
  rw [Nat.add_comm] at h
  have hr : (3 : ℝ)^v < (2 : ℝ)^(v+n) := by exact_mod_cast h
  have hh := Real.log_lt_log (by positivity) hr
  rw [Real.log_pow, Real.log_pow] at hh
  linarith

private theorem gap_from_log {n v : ℕ} (hv : 0 < v)
    (hL : 1/((2 : ℝ)^v-1) ≤ ((v+n : ℕ) : ℝ)*Real.log 2 - (v : ℝ)*Real.log 3) :
    3^v + 2^n ≤ 2^(n+v)+1 := by
  have h2 : 0 < (2 : ℝ)^v := by positivity
  have h3 : 0 < (3 : ℝ)^v := by positivity
  have hden : 0 < (2 : ℝ)^v-1 := sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega))
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < (2 : ℝ)^(v+n)/3^v)
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  have hratio : 1/((2 : ℝ)^v-1) ≤ (2^(v+n)-3^v)/3^v := by
    rw [sub_div, div_self (ne_of_gt h3)]
    exact hL.trans hlog
  rw [div_le_div_iff₀ hden h3, pow_add] at hratio
  have hr : (3 : ℝ)^v + 2^n ≤ 2^n*2^v := by
    by_contra! hh
    have hh' := mul_lt_mul_of_pos_left hh h2
    nlinarith only [hratio, hh']
  rw [← pow_add] at hr
  have : 3^v+2^n ≤ 2^(n+v) := by exact_mod_cast hr
  omega

-- A pair of rational bounds on log₂ 3 with determinant one. Both comparisons
-- reduce to comparisons of integers and are verified by the Lean kernel.
private theorem log_compare_powers {a b x y : ℕ} (ha : 0 < a) (h : a^x < b^y) :
    (x : ℝ)*Real.log a < (y : ℝ)*Real.log b := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have h' : (a : ℝ)^x < (b : ℝ)^y := by exact_mod_cast h
  simpa only [Real.log_pow] using Real.log_lt_log (pow_pos ha' x) h'

set_option exponentiation.threshold 80000 in
private theorem lower_power_check : (2 : ℕ)^50508 < 3^31867 := by decide

private theorem log_lower_rational : (50508 : ℝ)*Real.log 2 < 31867*Real.log 3 :=
  log_compare_powers (a := 2) (b := 3) (x := 50508) (y := 31867) (by decide) lower_power_check

set_option exponentiation.threshold 80000 in
private theorem upper_power_check : (3 : ℕ)^47468 < 2^75235 := by decide

private theorem log_upper_rational : (47468 : ℝ)*Real.log 3 < 75235*Real.log 2 :=
  log_compare_powers (a := 3) (b := 2) (x := 47468) (y := 75235) (by decide) upper_power_check

private theorem medium_log_lower {n v : ℕ} (hv : 18 ≤ v) (hmax : v ≤ 20000)
    (h : 3^v < 2^(n+v)) :
    1/((2 : ℝ)^v-1) ≤ ((v+n : ℕ) : ℝ)*Real.log 2 - (v : ℝ)*Real.log 3 := by
  have hv' : 0 < (v : ℝ) := by exact_mod_cast (by omega : 0 < v)
  have hlg : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp := positive_log_gap h
  have hlo := mul_lt_mul_of_pos_left log_lower_rational hv'
  have hhi := mul_lt_mul_of_pos_left log_upper_rational hv'
  have hlreal : (50508*(v : ℝ))*Real.log 2 < (31867*((v+n : ℕ) : ℝ))*Real.log 2 := by
    linarith only [hlo, hp]
  have hlnat : 50508*v < 31867*(v+n) := by
    exact_mod_cast (lt_of_mul_lt_mul_right hlreal (le_of_lt hlg))
  -- If 47468*(v+n) ≤ 75235*v, the determinant-one identity forces v ≥ 47468.
  have hgap : 75235*v + 1 ≤ 47468*(v+n) := by omega
  have hgap' : 75235*(v : ℝ)+1 ≤ 47468*((v+n : ℕ) : ℝ) := by exact_mod_cast hgap
  have hscaled := mul_le_mul_of_nonneg_right hgap' (le_of_lt hlg)
  have hexp : (262144 : ℝ) ≤ 2^v := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 2) hv : 2^18 ≤ 2^v)
  have hfrac : 1/((2 : ℝ)^v-1) ≤ 1/200000 := by
    apply (div_le_div_iff₀ (by linarith) (by norm_num)).mpr
    linarith
  linarith only [hfrac, hhi, hscaled, Real.log_two_gt_d9]

/-- An unconditional all-n estimate for the first 20,000 exponents v. -/
theorem gap_to_20000 {v : ℕ} (hv : 0 < v) (hmax : v ≤ 20000) : GapAt v := by
  intro n hn h
  by_cases hnv : v < n
  · exact gap_when_n_gt_v hv hnv
  by_cases hmed : 18 ≤ v
  · exact gap_from_log hv (medium_log_lower hmed hmax h)
  exact finite_gaps ⟨n, by omega⟩ ⟨v, by omega⟩ (by change n+v ≤ 34; omega) hn hv h

theorem gap_of_log_bound {v : ℕ} (hL : LargeLogBound) (hv : 0 < v) : GapAt v := by
  by_cases hmax : v ≤ 20000
  · exact gap_to_20000 hv hmax
  intro n _hn h
  have hl := hL v n (by omega)
  rw [abs_of_pos (positive_log_gap h)] at hl
  exact gap_from_log hv hl

end Jeffery
