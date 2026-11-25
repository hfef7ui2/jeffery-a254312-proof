module

public import Mathlib.Basic.ExistsUnique
public import Std.Tactic

public section

namespace Jeffery

/-- The number of positions before the diagonal with zero-based number `s`. -/
def triangular : Nat → Nat
  | 0 => 0
  | s + 1 => triangular s + s + 1

/-- Position of the entry in row `n`, column `k` in the upward antidiagonal
    reading order. All three indices are one-based. -/
def indexOfPosition (n k : Nat) : Nat := triangular (n + k - 2) + k

private def nextPosition : Nat × Nat → Nat × Nat
  | (0, c) => (c + 1, 0)
  | (r + 1, c) => (r, c + 1)

private def zeroBasedPosition : Nat → Nat × Nat
  | 0 => (0, 0)
  | t + 1 => nextPosition (zeroBasedPosition t)

/-- The positions start at `(1,1)` and run upward along each antidiagonal.
    After a position in the first row, the next diagonal starts in column one. -/
def positionAt (i : Nat) : Nat × Nat :=
  let p := zeroBasedPosition (i - 1)
  (p.1 + 1, p.2 + 1)

theorem positionAt_pos (i : Nat) : 0 < (positionAt i).1 ∧ 0 < (positionAt i).2 := by
  simp [positionAt]

theorem indexOfPosition_pos (n k : Nat) (hk : 0 < k) : 0 < indexOfPosition n k := by
  unfold indexOfPosition
  omega

private theorem triangular_mono {s t : Nat} (h : s ≤ t) : triangular s ≤ triangular t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simp
  | succ d ih =>
    change triangular s ≤ triangular (s + d) + (s + d) + 1
    omega

private theorem index_lt_of_diagonal_lt {n k n' k' : Nat} (hn : 0 < n) (hk : 0 < k)
    (hk' : 0 < k') (hd : n + k - 2 < n' + k' - 2) :
    indexOfPosition n k < indexOfPosition n' k' := by
  have h := triangular_mono (show (n + k - 2) + 1 ≤ n' + k' - 2 by omega)
  change triangular (n + k - 2) + (n + k - 2) + 1 ≤ triangular (n' + k' - 2) at h
  unfold indexOfPosition
  omega

theorem indexOfPosition_injective {n k n' k' : Nat}
    (hn : 0 < n) (hk : 0 < k) (hn' : 0 < n') (hk' : 0 < k')
    (h : indexOfPosition n k = indexOfPosition n' k') : (n,k) = (n',k') := by
  have hd : n + k - 2 = n' + k' - 2 := by
    rcases Nat.lt_trichotomy (n + k - 2) (n' + k' - 2) with hlt | he | hgt
    · have := index_lt_of_diagonal_lt hn hk hk' hlt
      omega
    · exact he
    · have := index_lt_of_diagonal_lt hn' hk' hk hgt
      omega
  unfold indexOfPosition at h
  rw [hd] at h
  exact Prod.ext (by dsimp; omega) (by dsimp; omega)

private theorem zeroBasedPosition_index (t : Nat) :
    triangular ((zeroBasedPosition t).1 + (zeroBasedPosition t).2) +
      (zeroBasedPosition t).2 = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    obtain ⟨r, c, he⟩ : ∃ r c, zeroBasedPosition t = (r, c) :=
      ⟨(zeroBasedPosition t).1, (zeroBasedPosition t).2, rfl⟩
    rw [zeroBasedPosition, he]
    rw [he] at ih
    cases r with
    | zero => simpa [nextPosition, triangular, Nat.add_assoc] using congrArg Nat.succ ih
    | succ r =>
      simp only [nextPosition, Nat.succ_add, Nat.add_succ] at ih ⊢
      omega

theorem indexOfPosition_positionAt (i : Nat) (hi : 0 < i) :
    indexOfPosition (positionAt i).1 (positionAt i).2 = i := by
  have h := zeroBasedPosition_index (i - 1)
  simp only [positionAt, indexOfPosition]
  rw [show (zeroBasedPosition (i - 1)).1 + 1 + ((zeroBasedPosition (i - 1)).2 + 1) - 2 =
    (zeroBasedPosition (i - 1)).1 + (zeroBasedPosition (i - 1)).2 by omega]
  omega

theorem positionAt_indexOfPosition (n k : Nat) (hn : 0 < n) (hk : 0 < k) :
    positionAt (indexOfPosition n k) = (n,k) := by
  have hp := positionAt_pos (indexOfPosition n k)
  exact indexOfPosition_injective hp.1 hp.2 hn hk
    (indexOfPosition_positionAt _ (indexOfPosition_pos n k hk))

theorem existsUnique_position_of_index (i : Nat) (hi : 0 < i) :
    ∃! p : Nat × Nat, 0 < p.1 ∧ 0 < p.2 ∧ indexOfPosition p.1 p.2 = i := by
  obtain ⟨hn, hk⟩ := positionAt_pos i
  have h := indexOfPosition_positionAt i hi
  refine ⟨positionAt i, ⟨hn, hk, h⟩, ?_⟩
  rintro ⟨n,k⟩ ⟨hn', hk', he⟩
  exact indexOfPosition_injective hn' hk' hn hk (he.trans h.symm)

/-- Unique occurrence in the one-based sequence is equivalent to unique
    occurrence among the positive positions of the array. -/
theorem unique_index_iff_unique_position (P : Nat → Nat → Prop) :
    (∃! i : Nat, 0 < i ∧ P (positionAt i).1 (positionAt i).2) ↔
      ∃! p : Nat × Nat, 0 < p.1 ∧ 0 < p.2 ∧ P p.1 p.2 := by
  constructor
  · rintro ⟨i, ⟨hi, hP⟩, only⟩
    obtain ⟨hn, hk⟩ := positionAt_pos i
    refine ⟨positionAt i, ⟨hn, hk, hP⟩, ?_⟩
    rintro ⟨n,k⟩ ⟨hn', hk', hP'⟩
    have hpos := positionAt_indexOfPosition n k hn' hk'
    have he := only (indexOfPosition n k) ⟨indexOfPosition_pos n k hk', by simpa [hpos] using hP'⟩
    exact hpos.symm.trans (congrArg positionAt he)
  · rintro ⟨⟨n,k⟩, ⟨hn, hk, hP⟩, only⟩
    have hpos := positionAt_indexOfPosition n k hn hk
    refine ⟨indexOfPosition n k, ⟨indexOfPosition_pos n k hk, by simpa [hpos] using hP⟩, ?_⟩
    rintro i ⟨hi, hP'⟩
    obtain ⟨hn', hk'⟩ := positionAt_pos i
    have he := only (positionAt i) ⟨hn', hk', hP'⟩
    have h := indexOfPosition_positionAt i hi
    rw [he] at h
    exact h.symm

end Jeffery
