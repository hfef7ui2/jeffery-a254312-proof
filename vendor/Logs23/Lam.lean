import Mathlib

namespace Steiner

noncomputable def Lam (k l : ℕ) : ℝ := ((k + l : ℕ) : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3

end Steiner
