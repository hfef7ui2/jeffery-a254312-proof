import Jeffery.Statement
import Jeffery.Gap
import Jeffery.Antidiagonal
import Logs23.TwoLog

namespace Jeffery

/-- The integral power-gap inequality, without any number-theoretic premise. -/
theorem dyadic_gap {n v : ℕ} (hn : 0 < n) (hv : 0 < v)
    (h : 3^v < 2^(n+v)) : 3^v + 2^n ≤ 2^(n+v) + 1 :=
  gap_of_log_bound Logs23.lam_lower_thm hv n hn h

/-- Jeffery's conjecture in OEIS A254312: exactly one positive ordered pair of
indices for each positive input whose original rational-valued step rises. -/
theorem jeffery_conjecture (m : ℕ) (hm : 0 < m) :
    (m : ℚ) < originalStep m ↔
      ∃! p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ oeisArray p.1 p.2 = (m : ℤ) := by
  rw [← step_as_printed, Nat.cast_lt]
  exact permutation_of_gap (fun _ _ hn hv h => dyadic_gap hn hv h) m hm

/-- In particular there is no occurrence at all for a nonascending input. -/
theorem ascent_iff_occurs (m : ℕ) (hm : 0 < m) :
    (m : ℚ) < originalStep m ↔
      ∃ n k : ℕ, 0 < n ∧ 0 < k ∧ oeisArray n k = (m : ℤ) := by
  rw [jeffery_conjecture m hm]
  constructor
  · rintro ⟨⟨n,k⟩, ⟨hn,hk,he⟩, _⟩
    exact ⟨n,k,hn,hk,he⟩
  · rintro ⟨n,k,hn,hk,he⟩
    obtain ⟨m',_,hentry,only⟩ := entry_has_unique_position n k hn hk
    have hmm : m' = m := by exact_mod_cast hentry.symm.trans he
    subst m'
    refine ⟨(n,k), ⟨hn,hk,he⟩, ?_⟩
    rintro ⟨i,j⟩ ⟨hi,hj,hij⟩
    exact Prod.ext (only i j hi hj hij).1 (only i j hi hj hij).2

/-- The one-based sequence obtained by reading the array in upward antidiagonals. -/
noncomputable def sequenceEntry (i : ℕ) : ℤ :=
  oeisArray (positionAt i).1 (positionAt i).2

/-- In the original one-dimensional indexing, each ascent occurs exactly once. -/
theorem jeffery_sequence (m : ℕ) (hm : 0 < m) :
    (m : ℚ) < originalStep m ↔ ∃! i : ℕ, 0 < i ∧ sequenceEntry i = (m : ℤ) := by
  exact (jeffery_conjecture m hm).trans
    (unique_index_iff_unique_position (fun n k => oeisArray n k = (m : ℤ))).symm

end Jeffery

#print axioms Jeffery.dyadic_gap
#print axioms Jeffery.entry_has_unique_position
#print axioms Jeffery.jeffery_conjecture
#print axioms Jeffery.ascent_iff_occurs
#print axioms Jeffery.jeffery_sequence
