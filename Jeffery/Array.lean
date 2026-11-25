module

public import Mathlib.Basic.ExistsUnique
public import Std.Tactic

public section

namespace Jeffery

/-- The correction to the column parameter in row `n = r + 1`.
    It is zero for even `n`, one for odd `n` and even `a`, and two otherwise. -/
def rowCorrection (r a : Nat) : Nat :=
  if r % 2 = 1 then 0 else if a % 2 = 0 then 1 else 2

def rowParameter (r a k : Nat) : Nat := 3 * k - rowCorrection r a

/-- The OEIS entry with its parity correction simplified and its common factor
    of two cancelled. Here `r + 1` is the one-based row index. -/
def arrayEntry (r a k : Nat) : Nat :=
  (2^a * rowParameter r a k + 2 - 2^r) / 3

private theorem powTwo_mod_three (r : Nat) :
    2^r % 3 = if r % 2 = 0 then 1 else 2 := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]
    have hr := Nat.mod_lt r (by decide : 0 < 2)
    split <;> rename_i h <;> split <;> omega

private theorem correction_le (r a : Nat) : rowCorrection r a ≤ 2 := by
  unfold rowCorrection
  split <;> simp_all
  split <;> decide

theorem parameter_pos (r a k : Nat) (hk : 0 < k) :
    0 < rowParameter r a k := by
  have h := correction_le r a
  unfold rowParameter
  omega

/-- Integrality of the original row formula amounts to this residue condition. -/
private theorem row_residue_iff (r a t : Nat) :
    (2^a * t + 2) % 3 = 2^r % 3 ↔ (t + rowCorrection r a) % 3 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod, powTwo_mod_three, powTwo_mod_three]
  have hr := Nat.mod_lt r (by decide : 0 < 2)
  have ha := Nat.mod_lt a (by decide : 0 < 2)
  have ht := Nat.mod_lt t (by decide : 0 < 3)
  unfold rowCorrection
  by_cases hp : r % 2 = 0 <;> by_cases hq : a % 2 = 0 <;>
    simp [hp, hq, show (r % 2 = 1) ↔ ¬(r % 2 = 0) by omega] <;> omega

private theorem parameter_exact (r a k : Nat) (hk : 0 < k) :
    rowParameter r a k + rowCorrection r a = 3 * k := by
  have h := correction_le r a
  unfold rowParameter
  omega

/-- The product on the right gives the exact quotient represented by the row.
    In particular the apparent division in `arrayEntry` is exact. -/
theorem arrayEntry_eqn {r a k : Nat} (ha : r + 1 ≤ a) (hk : 0 < k) :
    3 * arrayEntry r a k + 2^r = 2^a * rowParameter r a k + 2 := by
  have hp := parameter_pos r a k hk
  have hbound : 2^r ≤ 2^a * rowParameter r a k :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : r ≤ a))
      (Nat.le_mul_of_pos_right _ hp)
  have hres := (row_residue_iff r a (rowParameter r a k)).2 (by
    rw [parameter_exact r a k hk]
    omega)
  unfold arrayEntry
  omega

/-- The row lists, exactly once, every positive integral parameter compatible
    with the divisibility condition `2^a ∣ 3*m + 2^r − 2`. -/
theorem row_unique_iff {r a m : Nat} (ha : r + 1 ≤ a) :
    (∃! k : Nat, 0 < k ∧ arrayEntry r a k = m) ↔
      ∃ t : Nat, 0 < t ∧ 3*m + 2^r = 2^a*t + 2 := by
  constructor
  · rintro ⟨k, ⟨hk, hmk⟩, _⟩
    subst m
    exact ⟨rowParameter r a k, parameter_pos r a k hk, arrayEntry_eqn ha hk⟩
  · rintro ⟨t, ht, he⟩
    have hres : (2^a*t + 2) % 3 = 2^r % 3 := by omega
    have hd := (row_residue_iff r a t).1 hres
    let k := (t + rowCorrection r a) / 3
    have htk : 3*k = t + rowCorrection r a := by dsimp [k]; omega
    have hk : 0 < k := by omega
    have hp : rowParameter r a k = t := by
      unfold rowParameter
      omega
    have hval := arrayEntry_eqn ha hk
    rw [hp] at hval
    refine ⟨k, ⟨hk, by omega⟩, ?_⟩
    rintro j ⟨hj, hjm⟩
    have hjval := arrayEntry_eqn ha hj
    rw [hjm, he] at hjval
    have hjp := Nat.mul_left_cancel (Nat.two_pow_pos a) (Nat.add_right_cancel hjval)
    have hjexact := parameter_exact r a j hj
    omega

theorem arrayEntry_pos {r a k : Nat} (ha : r + 1 ≤ a) (hk : 0 < k) :
    0 < arrayEntry r a k := by
  have hm := arrayEntry_eqn ha hk
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : r ≤ a)
  have hprod := Nat.le_mul_of_pos_right (2^a) (parameter_pos r a k hk)
  omega

private theorem sign_of_parity (j : Nat) :
    (-1 : Int)^j = if j % 2 = 0 then 1 else -1 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Int.pow_succ, ih]
    have hj := Nat.mod_lt j (by decide : 0 < 2)
    split <;> split <;> omega

/-- Recover the signed parity factor in the OEIS definition, using integers
    so the powers of minus one have their usual meaning. -/
private theorem signed_factor {r a k : Nat} (hk : 0 < k) :
    6*(k : Int) - (3 - (-1 : Int)^a) * (1 - (-1 : Int)^(r+1)) / 2 =
      2*(rowParameter r a k : Int) := by
  rw [sign_of_parity, sign_of_parity]
  have h := parameter_exact r a k hk
  unfold rowCorrection at h
  have hr := Nat.mod_lt r (by decide : 0 < 2)
  by_cases h₁ : r % 2 = 1 <;> by_cases h₂ : a % 2 = 0 <;>
    simp [h₁, h₂, show ((r+1) % 2 = 0) ↔ (r % 2 = 1) by omega] at h ⊢ <;>
    omega

/-- The numerator of the original OEIS formula equals six times the entry. -/
theorem arrayEntry_oeis_numerator {r a k : Nat} (ha : r + 1 ≤ a) (hk : 0 < k) :
    6*(arrayEntry r a k : Int) =
      (2 : Int)^a *
        (6*(k : Int) - (3 - (-1 : Int)^a) * (1 - (-1 : Int)^(r+1)) / 2)
        - 2^(r+1) + 4 := by
  rw [signed_factor hk, Int.pow_succ]
  rw [Int.two_mul, Int.mul_add]
  have h := congrArg (fun x : Nat => (x : Int)) (arrayEntry_eqn ha hk)
  simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at h
  change 3*(arrayEntry r a k : Int) + (2 : Int)^r =
    (2 : Int)^a*(rowParameter r a k : Int) + 2 at h
  omega

/-- Exact equality with the original OEIS formula, for `n = r + 1`. -/
theorem arrayEntry_oeis {r a k : Nat} (ha : r + 1 ≤ a) (hk : 0 < k) :
    (arrayEntry r a k : Int) =
      ((2 : Int)^a *
        (6*(k : Int) - (3 - (-1 : Int)^a) * (1 - (-1 : Int)^(r+1)) / 2)
        - 2^(r+1) + 4) / 6 := by
  rw [← arrayEntry_oeis_numerator ha hk]
  omega

end Jeffery
