import Jeffery.Permutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace Jeffery

/-- The original formula in A257480, evaluated in the rationals so that
`3 / 2` and the final division by six are ordinary fractions. -/
def originalStep (m : ℕ) : ℚ :=
  let u := 1 + acceleratedStep (4*m-3)
  (3 + (3/2 : ℚ) ^ valuationTwo u * u) / 6

theorem step_as_printed (m : ℕ) : (jefferyStep m : ℚ) = originalStep m := by
  obtain ⟨r,t,ht,hrt⟩ := decompose_two (3*(4*m-3)+1) (by omega)
  have hf : acceleratedStep (4*m-3) = t := by
    unfold acceleratedStep
    rw [hrt, oddPart_pow_mul ht]
  obtain ⟨v,q,hq,he⟩ := decompose_two (1+t) (by omega)
  have hv : 0 < v := by
    cases v with
    | zero => simp at he; omega
    | succ v => omega
  change ((jefferyStep m : ℕ) : ℚ) = _
  unfold jefferyStep originalStep
  dsimp only
  rw [hf, he, valuationTwo_pow_mul hq, oddPart_pow_mul hq]
  have h6 := numerator_exact hv hq
  have h6q := congrArg (fun j : ℕ => (j : ℚ)) h6
  push_cast at h6q ⊢
  rw [div_pow]
  field_simp
  linear_combination h6q

end Jeffery
