import Std

namespace Jeffery

/-- The number of successive exact divisions by two. The value at zero is a
convention; all uses in the OEIS formula are on strictly positive integers. -/
def valuationTwo (x : Nat) : Nat :=
  if x = 0 ∨ x % 2 = 1 then 0 else valuationTwo (x / 2) + 1
termination_by x
decreasing_by omega

/-- Remove the entire power of two from an integer. -/
def oddPart (x : Nat) := x / 2 ^ valuationTwo x

def acceleratedStep (x : Nat) := oddPart (3*x+1)

/-- A257480. The factor (3/2)^v * u is evaluated as 3^v * (u/2^v). -/
def jefferyStep (m : Nat) : Nat :=
  let u := 1 + acceleratedStep (4*m-3)
  (3 + 3 ^ valuationTwo u * oddPart u) / 6

theorem valuationTwo_pow_mul {k q : Nat} (hq : q % 2 = 1) :
    valuationTwo (2^k*q) = k := by
  induction k with
  | zero => simp only [Nat.pow_zero, Nat.one_mul]; rw [valuationTwo]; simp [hq]
  | succ k ih =>
    have hq0 : 0 < q := by omega
    have hpos : 0 < 2^k*q := Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2)) hq0
    rw [Nat.pow_succ', Nat.mul_assoc, valuationTwo, ite_eq_right_iff.mpr (by omega)]
    rw [show 2*(2^k*q)/2 = 2^k*q by omega, ih]

theorem oddPart_pow_mul {k q : Nat} (hq : q % 2 = 1) :
    oddPart (2^k*q) = q := by
  unfold oddPart
  rw [valuationTwo_pow_mul hq, Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide : 0 < 2))]

theorem decompose_two (x : Nat) (hx : 0 < x) :
    ∃ k q : Nat, q % 2 = 1 ∧ x = 2^k*q := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases h : x % 2 = 1
    · exact ⟨0, x, h, by simp⟩
    · have hx' : 0 < x/2 := by omega
      obtain ⟨k, q, hq, he⟩ := ih (x/2) (by omega) hx'
      refine ⟨k+1, q, hq, ?_⟩
      rw [Nat.pow_succ', Nat.mul_assoc, ← he]
      omega

private theorem three_pow_odd (k : Nat) : 3^k % 2 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

theorem numerator_exact {v q : Nat} (hv : 0 < v) (hq : q % 2 = 1) :
    6*((3+3^v*q)/6) = 3+3^v*q := by
  cases v with
  | zero => omega
  | succ w =>
    have hpow := three_pow_odd w
    have hprod : (3^w*q) % 2 = 1 := by
      rw [Nat.mul_mod, hpow, hq]
    rw [Nat.pow_succ', Nat.mul_assoc]
    omega

theorem normalization_from_factors {m r v q : Nat} (hm : 0 < m) (hv : 0 < v)
    (hq : q % 2 = 1) (h : 3*m-2 = 2^r*(2^v*q-1)) :
    valuationTwo (3*m-2) = r ∧
      6*jefferyStep m = 3+3^v*q := by
  have hqpos : 0 < q := by omega
  have hpos : 0 < 2^v*q := Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2)) hqpos
  have hodd : (2^v*q-1) % 2 = 1 := by
    cases v with
    | zero => omega
    | succ v =>
      have htpos : 0 < 2^v*q := Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2)) hqpos
      rw [Nat.pow_succ', Nat.mul_assoc]
      omega
  have ha : 3*(4*m-3)+1 = 2^(2+r)*(2^v*q-1) := by
    rw [Nat.pow_add, Nat.mul_assoc, ← h]
    change 3*(4*m-3)+1 = 4*(3*m-2)
    omega
  have hf : acceleratedStep (4*m-3) = 2^v*q-1 := by
    unfold acceleratedStep
    rw [ha, oddPart_pow_mul hodd]
  have hu : 1+acceleratedStep (4*m-3) = 2^v*q := by rw [hf]; omega
  constructor
  · rw [h, valuationTwo_pow_mul hodd]
  · unfold jefferyStep
    dsimp only
    rw [hu, valuationTwo_pow_mul hq, oddPart_pow_mul hq]
    exact numerator_exact hv hq

theorem normalization (m : Nat) (hm : 0 < m) :
    ∃ r v q : Nat, 0 < v ∧ q % 2 = 1 ∧
      3*m-2 = 2^r*(2^v*q-1) ∧ 6*jefferyStep m = 3+3^v*q := by
  obtain ⟨r, t, ht, hrt⟩ := decompose_two (3*m-2) (by omega)
  obtain ⟨v, q, hq, hvq⟩ := decompose_two (t+1) (by omega)
  have hv : 0 < v := by
    cases v with
    | zero => simp at hvq; omega
    | succ v => omega
  have h : 3*m-2 = 2^r*(2^v*q-1) := by
    rw [← hvq, Nat.add_sub_cancel]
    exact hrt
  exact ⟨r, v, q, hv, hq, h, (normalization_from_factors hm hv hq h).2⟩

end Jeffery
