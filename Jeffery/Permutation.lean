import Jeffery.Normalization
import Jeffery.Beatty
import Jeffery.Array
import Mathlib.Data.Nat.Prime.Basic

namespace Jeffery

/-- A254312, with both indices starting at one. Integer arithmetic keeps the
two signs and the divisions in the printed formula. -/
noncomputable def oeisArray (n k : ℕ) : ℤ :=
  let a := beatty n
  ((2 : ℤ)^a * (6*(k : ℤ) - (3 - (-1 : ℤ)^a) * (1 - (-1 : ℤ)^n) / 2)
    - 2^n + 4) / 6

private theorem row_as_printed (r k : ℕ) (hk : 0 < k) :
    (arrayEntry r (beatty (r+1)) k : ℤ) = oeisArray (r+1) k := by
  exact arrayEntry_oeis (by have := two_mul_le_beatty (r+1); omega) hk

private theorem factor_sum {m r v q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (h : 3*m-2 = 2^r*(2^v*q-1)) :
    3*m + 2^r = 2^(r+v)*q + 2 := by
  have hp : 0 < 2^v*q := Nat.mul_pos (Nat.two_pow_pos _) hq
  have he : 3*m-2 + 2^r = 2^(r+v)*q := by
    rw [h, pow_add, Nat.mul_assoc, ← Nat.mul_succ]
    congr 1
    omega
  omega

/-- Determine the sign of the difference without taking a truncated difference
of coefficients in the natural numbers. -/
private theorem ascend_iff_power {m r v q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (h : 3*m-2 = 2^r*(2^v*q-1)) (hs : 6*jefferyStep m = 3+3^v*q)
    (hgap : 3^v < 2^(r+1+v) → 3^v + 2^(r+1) ≤ 2^(r+1+v)+1) :
    m < jefferyStep m ↔ 2^(r+1+v) < 3^v := by
  have hsum := factor_sum hm hq h
  have hpow : (2 : ℕ)^(r+1+v) = 2 * 2^(r+v) := by
    rw [show r+1+v = (r+v)+1 by omega, Nat.pow_succ']
  have ht : 6*m + 2^(r+1) = 2^(r+1+v)*q + 4 := by
    rw [hpow, Nat.pow_succ', Nat.mul_assoc]
    omega
  have hp : 0 < (2 : ℕ)^(r+1) := Nat.two_pow_pos _
  have hne : (3 : ℕ)^v ≠ 2^(r+1+v) := by
    have odd3 : Odd ((3 : ℕ)^v) := (show Odd (3 : ℕ) by decide).pow
    have even2 : Even ((2 : ℕ)^(r+1+v)) := ⟨2^(r+v), by rw [hpow]; omega⟩
    intro he
    exact (Nat.not_odd_iff_even.mpr even2) (he ▸ odd3)
  constructor
  · intro hm'
    by_contra! hle
    have hg := hgap (lt_of_le_of_ne hle hne)
    have hle' : 3^v + (2^(r+1)-1) ≤ 2^(r+1+v) := by omega
    have hmul := Nat.mul_le_mul_right q hle'
    rw [Nat.add_mul] at hmul
    have := Nat.le_mul_of_pos_right (2^(r+1)-1) hq
    omega
  · intro hlt
    have := Nat.mul_lt_mul_of_pos_right hlt hq
    omega

private theorem row_for_factors {m r v q : ℕ} (hm : 0 < m) (hq : q % 2 = 1)
    (h : 3*m-2 = 2^r*(2^v*q-1)) :
    (∃! k : ℕ, 0 < k ∧ arrayEntry r (beatty (r+1)) k = m) ↔
      beatty (r+1) ≤ r+v := by
  have hq' : 0 < q := by omega
  have hsum := factor_sum hm hq' h
  have ha := two_mul_le_beatty (r+1)
  rw [row_unique_iff (by omega)]
  constructor
  · rintro ⟨t, _, ht⟩
    have hd : 2^(beatty (r+1)) ∣ 2^(r+v)*q := ⟨t, by omega⟩
    have hcop : Nat.Coprime (2^(beatty (r+1))) q :=
      (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hq)).pow_left _
    exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp
      (hcop.dvd_of_dvd_mul_right hd)
  · intro hle
    refine ⟨2^(r+v-beatty (r+1))*q, Nat.mul_pos (Nat.two_pow_pos _) hq', ?_⟩
    rw [← Nat.mul_assoc, ← pow_add, show beatty (r+1)+(r+v-beatty (r+1)) = r+v by omega]
    exact hsum

private theorem recover_row {m r k : ℕ} (hk : 0 < k)
    (h : arrayEntry r (beatty (r+1)) k = m) :
    valuationTwo (3*m-2) = r := by
  let a := beatty (r+1)
  have ha : r+1 ≤ a := by dsimp [a]; have := two_mul_le_beatty (r+1); omega
  let t := rowParameter r a k
  have ht : 0 < t := parameter_pos r a k hk
  have he := arrayEntry_eqn (r := r) (a := a) ha hk
  change arrayEntry r a k = m at h
  rw [h] at he
  change 3*m+2^r = 2^a*t+2 at he
  have hex : 2^a*t = 2^r*(2*(2^(a-(r+1))*t)) := by
    rw [← Nat.mul_assoc 2, ← Nat.pow_succ', ← Nat.mul_assoc, ← pow_add]
    congr 2
    omega
  let u := 2*(2^(a-(r+1))*t)-1
  have hu : u % 2 = 1 := by
    have := Nat.mul_pos (Nat.two_pow_pos (a-(r+1))) ht
    dsimp [u]; omega
  have hfac : 3*m-2 = 2^r*u := by
    have hpos := Nat.mul_pos (Nat.two_pow_pos (a-(r+1))) ht
    have hsucc : u+1 = 2*(2^(a-(r+1))*t) := by dsimp [u]; omega
    rw [hex, ← hsucc, Nat.mul_succ] at he
    omega
  rw [hfac, valuationTwo_pow_mul hu]

/-- All actual entries are positive integers, and any two positions for the
same entry agree. This excludes spurious entries of multiplicity greater
than one, independently of the ascent test. -/
theorem entry_has_unique_position (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    ∃ m : ℕ, 0 < m ∧ oeisArray n k = (m : ℤ) ∧
      ∀ i j : ℕ, 0 < i → 0 < j → oeisArray i j = (m : ℤ) → i = n ∧ j = k := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let a := beatty (r+1)
  let m := arrayEntry r a k
  have ha : r+1 ≤ a := by dsimp [a]; have := two_mul_le_beatty (r+1); omega
  have hm : 0 < m := arrayEntry_pos ha hk
  refine ⟨m, hm, (row_as_printed r k hk).symm, ?_⟩
  intro i j hi hj he
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rw [← row_as_printed s j hj] at he
  have hval : arrayEntry s (beatty (s+1)) j = m := by exact_mod_cast he
  have hrow : valuationTwo (3*m-2) = r := recover_row hk rfl
  have hsr : s = r := (recover_row hj hval).symm.trans hrow
  subst s
  have hur := (row_unique_iff (m:=m) ha).2
    ⟨rowParameter r a k, parameter_pos r a k hk, arrayEntry_eqn ha hk⟩
  obtain ⟨c, _, hc⟩ := hur
  exact ⟨rfl, (hc j ⟨hj, hval⟩).trans (hc k ⟨hk, rfl⟩).symm⟩

/-- Parameterized arithmetic lemma; the public theorem supplies the power gap. -/
theorem permutation_of_gap
    (gap : ∀ n v : ℕ, 0 < n → 0 < v → 3^v < 2^(n+v) → 3^v+2^n ≤ 2^(n+v)+1)
    (m : ℕ) (hm : 0 < m) :
    m < jefferyStep m ↔
      ∃! p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ oeisArray p.1 p.2 = (m : ℤ) := by
  obtain ⟨r,v,q,hv,hq,hfac,hs⟩ := normalization m hm
  have hr := (normalization_from_factors hm hv hq hfac).1
  have hrow := row_for_factors hm hq hfac
  have hcmp := comparison_iff_beatty_lt (r+1) v
  have hasc := ascend_iff_power hm (by omega) hfac hs (gap (r+1) v (by omega) hv)
  have iffrow : m < jefferyStep m ↔
      ∃! k : ℕ, 0 < k ∧ arrayEntry r (beatty (r+1)) k = m := by
    rw [hasc, hcmp, hrow]
    omega
  rw [iffrow]
  constructor
  · rintro ⟨k, ⟨hk, hkm⟩, huniq⟩
    refine ⟨(r+1,k), ⟨by simp, hk, ?_⟩, ?_⟩
    · rw [← row_as_printed r k hk, hkm]
    · rintro ⟨n,j⟩ ⟨hn,hj,he⟩
      cases n with
      | zero => exact (Nat.lt_irrefl _ hn).elim
      | succ s =>
        change oeisArray (s+1) j = (m : ℤ) at he
        rw [← row_as_printed s j hj] at he
        have hmj : arrayEntry s (beatty (s+1)) j = m := by exact_mod_cast he
        have hsr := recover_row hj hmj
        have : s = r := hsr.symm.trans hr
        clear hsr
        subst s
        simp [huniq j ⟨hj, hmj⟩]
  · rintro ⟨⟨n,k⟩, ⟨hn,hk,he⟩, huniq⟩
    cases n with
    | zero => exact (Nat.lt_irrefl _ hn).elim
    | succ s =>
      change oeisArray (s+1) k = (m : ℤ) at he
      rw [← row_as_printed s k hk] at he
      have hmk : arrayEntry s (beatty (s+1)) k = m := by exact_mod_cast he
      have : s = r := (recover_row hk hmk).symm.trans hr
      subst s
      refine ⟨k, ⟨hk, hmk⟩, ?_⟩
      rintro j ⟨hj,hjm⟩
      exact congrArg Prod.snd (huniq (r+1,j) ⟨by simp, hj, by
        rw [← row_as_printed r j hj, hjm]⟩)

end Jeffery
