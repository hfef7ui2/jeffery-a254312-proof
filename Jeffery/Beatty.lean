import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace Jeffery

/-- The exponent from OEIS A117630, with the ordinary natural floor. -/
noncomputable def beatty (n : ℕ) : ℕ :=
  ⌊(n : ℝ) * Real.log 3 / Real.log (3 / 2)⌋₊

theorem two_mul_le_beatty (n : ℕ) : 2 * n ≤ beatty n := by
  have hp : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hc : 2 * Real.log (3 / 2) ≤ Real.log 3 := by
    have h := Real.log_le_log (x := (3 / 2 : ℝ) ^ 2) (y := 3) (by norm_num) (by norm_num)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  apply Nat.le_floor
  push_cast
  apply (le_div_iff₀ hp).2
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr hc)]

/-- The strict power comparison is exactly the threshold given by the floor. -/
theorem comparison_iff_beatty_lt (n v : ℕ) :
    (2 : ℕ) ^ (n + v) < 3 ^ v ↔ beatty n < n + v := by
  have hp : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hn : 0 ≤ (n : ℝ) * Real.log 3 / Real.log (3 / 2) := by positivity
  have he := Real.log_div (x := (3 : ℝ)) (y := 2) (by norm_num) (by norm_num)
  have hlog :
      (2 : ℕ) ^ (n + v) < 3 ^ v ↔
        ((n : ℝ) + v) * Real.log 2 < (v : ℝ) * Real.log 3 := by
    calc
      _ ↔ (2 : ℝ) ^ (n + v) < 3 ^ v := by norm_cast
      _ ↔ Real.log ((2 : ℝ) ^ (n + v)) < Real.log ((3 : ℝ) ^ v) :=
        (Real.log_lt_log_iff (by positivity) (by positivity)).symm
      _ ↔ _ := by simp [Real.log_pow]
  rw [hlog, beatty, Nat.floor_lt hn, div_lt_iff₀ hp, Nat.cast_add, he]
  constructor <;> intro h <;> linarith only [h]

end Jeffery
