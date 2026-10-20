import LakeLevel.Spec.Calendar
import LakeLevel.Impl.Calendar

/-!
# Helper lemmas for the calendar proofs

The hard step in inverting Hinnant's formula is recovering the year-of-era
from the day-of-era. `omega` cannot do it in one go, so it is split into a
general fact (`yoeOf` is monotone, which `omega` proves) and a finite one
(it is right at both ends of each of the 400 era-years, checked exhaustively
by the kernel with `decide +kernel`).
-/

namespace LakeLevel.Cal

/-- Year-of-era from day-of-era, as in `ofDays0`. -/
def yoeOf (doe : Nat) : Nat := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365

/-- First day-of-era of era-year `yoe`. -/
def start (yoe : Nat) : Nat := yoe * 365 + yoe / 4 - yoe / 100

/-- Length of shifted (March-based) era-year `yoe`: it ends with the February
of Gregorian year `yoe + 1` (mod 400). -/
def len (yoe : Nat) : Nat := if leap (yoe + 1) then 366 else 365

theorem yoeOf_succ (a : Nat) : yoeOf a ≤ yoeOf (a + 1) := by
  unfold yoeOf; omega

theorem yoeOf_mono {a b : Nat} (hab : a ≤ b) : yoeOf a ≤ yoeOf b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le hab with h1 | h1
    · exact Nat.le_trans (ih (by omega)) (yoeOf_succ n)
    · subst h1; exact Nat.le_refl _

/-- The finite part, checked by the kernel for all 400 era-years. -/
theorem endpoints : ∀ y, y < 400 →
    yoeOf (start y) = y ∧ yoeOf (start y + len y - 1) = y ∧
    (y < 399 → start y + len y = start (y + 1)) ∧ (y = 399 → start y + len y = 146097) := by
  decide +kernel

theorem yoeOf_eq {yoe doy : Nat} (hy : yoe < 400) (hd : doy < len yoe) :
    yoeOf (start yoe + doy) = yoe := by
  have ⟨e1, e2, _, _⟩ := endpoints yoe hy
  have := yoeOf_mono (a := start yoe) (b := start yoe + doy) (by omega)
  have := yoeOf_mono (a := start yoe + doy) (b := start yoe + len yoe - 1) (by omega)
  omega

/-- Conversely, `yoeOf doe` locates `doe` inside its era-year. -/
theorem yoeOf_bounds {doe : Nat} (hd : doe < 146097) :
    yoeOf doe < 400 ∧ start (yoeOf doe) ≤ doe ∧ doe < start (yoeOf doe) + len (yoeOf doe) := by
  have h400 : yoeOf doe < 400 := by unfold yoeOf; omega
  refine ⟨h400, ?_, ?_⟩
  · -- if doe < start y then yoeOf doe ≤ y - 1
    apply Nat.le_of_not_lt; intro hlt
    have hy0 : yoeOf doe ≠ 0 := by intro h0; rw [h0] at hlt; simp [start] at hlt
    have ⟨_, e2, e3, _⟩ := endpoints (yoeOf doe - 1) (by omega)
    have e3 := e3 (by omega)
    rw [show yoeOf doe - 1 + 1 = yoeOf doe by omega] at e3
    have := yoeOf_mono (a := doe) (b := start (yoeOf doe - 1) + len (yoeOf doe - 1) - 1) (by omega)
    omega
  · apply Nat.lt_of_not_le; intro hge
    by_cases h399 : yoeOf doe = 399
    · have ⟨_, _, _, e4⟩ := endpoints 399 (by omega)
      rw [h399] at hge; have := e4 rfl; omega
    · have ⟨_, _, e3, _⟩ := endpoints (yoeOf doe) h400
      have e3 := e3 (by omega)
      have ⟨e1, _, _, _⟩ := endpoints (yoeOf doe + 1) (by omega)
      have := yoeOf_mono (a := start (yoeOf doe + 1)) (b := doe) (by omega)
      omega

theorem start_add_len_le {yoe : Nat} (hy : yoe < 400) : start yoe + len yoe ≤ 146097 := by
  have ⟨_, _, e3, e4⟩ := endpoints yoe hy
  by_cases h : yoe = 399
  · exact Nat.le_of_eq (e4 h)
  · rw [e3 (by omega)]; unfold start; omega

/-- `ofDays0`, given a day split into era / era-year / day-of-year. -/
theorem ofDays0_split (era yoe doy : Nat) (hy : yoe < 400) (hd : doy < len yoe) :
    ofDays0 (era * 146097 + (start yoe + doy)) =
      (if (if (5 * doy + 2) / 153 < 10 then (5 * doy + 2) / 153 + 3 else (5 * doy + 2) / 153 - 9) ≤ 2
        then yoe + era * 400 + 1 else yoe + era * 400,
       if (5 * doy + 2) / 153 < 10 then (5 * doy + 2) / 153 + 3 else (5 * doy + 2) / 153 - 9,
       doy - (153 * ((5 * doy + 2) / 153) + 2) / 5 + 1) := by
  have hle := start_add_len_le hy
  have h1 : (era * 146097 + (start yoe + doy)) / 146097 = era := by omega
  have h2 : (era * 146097 + (start yoe + doy)) % 146097 = start yoe + doy := by omega
  have h3 := yoeOf_eq hy hd
  unfold yoeOf at h3
  have h4 : start yoe + doy - (365 * yoe + yoe / 4 - yoe / 100) = doy := by unfold start; omega
  simp only [ofDays0, h1, h2, h3, h4]

/-- The pieces of `daysFrom0`, named. -/
def Ysh (y mo : Nat) : Nat := if mo ≤ 2 then y - 1 else y
def MP (mo : Nat) : Nat := if mo > 2 then mo - 3 else mo + 9
def DOY (mo d : Nat) : Nat := (153 * MP mo + 2) / 5 + d - 1

theorem daysFrom0_split (y mo d : Nat) :
    daysFrom0 y mo d = Ysh y mo / 400 * 146097 + (start (Ysh y mo % 400) + DOY mo d) := rfl

/-- Forward round trip: `ofDays0` inverts `daysFrom0` on valid dates. -/
theorem ofDays0_daysFrom0 {y mo d : Nat} (h : ValidDate y mo d) :
    ofDays0 (daysFrom0 y mo d) = (y, mo, d) := by
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := h
  rw [daysFrom0_split]
  have hmo : mo = 1 ∨ mo = 2 ∨ mo = 3 ∨ mo = 4 ∨ mo = 5 ∨ mo = 6 ∨ mo = 7 ∨ mo = 8 ∨
      mo = 9 ∨ mo = 10 ∨ mo = 11 ∨ mo = 12 := by omega
  have hlen : DOY mo d < len (Ysh y mo % 400) := by
    rcases hmo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp (config := {decide := true}) only [DOY, MP, Ysh, len, dim, leap, ↓reduceIte] at hd2 ⊢
      repeat' split at hd2
      all_goals (repeat' split) <;> omega
  rw [ofDays0_split _ _ _ (Nat.mod_lt _ (by omega)) hlen]
  rcases hmo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (config := {decide := true}) only [DOY, MP, Ysh, dim, leap, ↓reduceIte] at hd2 ⊢
    repeat' split at hd2
    all_goals (repeat' split) <;> simp only [Prod.mk.injEq] <;> omega

/-- Reverse round trip: from day 306 (0001-01-01) on, `ofDays0` yields a valid
date that `daysFrom0` maps back. -/
theorem ofDays0_valid_inv (z : Nat) (hz : 306 ≤ z) :
    ValidDate (ofDays0 z).1 (ofDays0 z).2.1 (ofDays0 z).2.2 ∧
    daysFrom0 (ofDays0 z).1 (ofDays0 z).2.1 (ofDays0 z).2.2 = z := by
  obtain ⟨hy, hs, hl⟩ := yoeOf_bounds (Nat.mod_lt z (by decide : 146097 > 0))
  obtain ⟨era, yoe, doy, hyoe, hdoy, rfl⟩ : ∃ era yoe doy, yoe < 400 ∧ doy < len yoe ∧
      z = era * 146097 + (start yoe + doy) :=
    ⟨z / 146097, yoeOf (z % 146097), z % 146097 - start (yoeOf (z % 146097)), hy, by omega, by omega⟩
  clear hy hs hl
  rw [ofDays0_split _ _ _ hyoe hdoy]
  have hk : (5 * doy + 2) / 153 < 12 := by unfold len at hdoy; split at hdoy <;> omega
  generalize hkk : (5 * doy + 2) / 153 = k at hk ⊢
  unfold start at hz
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨
      k = 9 ∨ k = 10 ∨ k = 11 := by omega
  have e1 : start ((yoe + era * 400) % 400) = start yoe := by
    rw [show (yoe + era * 400) % 400 = yoe by omega]
  have e2 : start ((yoe + era * 400 + 1 - 1) % 400) = start yoe := by
    rw [show (yoe + era * 400 + 1 - 1) % 400 = yoe by omega]
  rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (config := {decide := true}) only [↓reduceIte, daysFrom0_split, DOY, MP, Ysh,
      ValidDate, dim, leap, len, true_and] at hdoy ⊢
    repeat' apply And.intro
    all_goals
      repeat' split at hdoy
      all_goals (repeat' split) <;> omega

/-- Every valid date is on or after day 306 (0001-01-01). -/
theorem daysFrom0_ge {y mo d : Nat} (h : ValidDate y mo d) : 306 ≤ daysFrom0 y mo d := by
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := h
  simp only [daysFrom0_split, Ysh, DOY, MP, start]
  split <;> split <;> omega

/-- Tomorrow is one more day. -/
theorem daysFrom0_next {y mo d : Nat} (h : ValidDate y mo d) :
    daysFrom0 (nextDate y mo d).1 (nextDate y mo d).2.1 (nextDate y mo d).2.2 =
      daysFrom0 y mo d + 1 := by
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := h
  unfold nextDate
  split
  · simp only [daysFrom0_split, DOY]; omega
  · split
    · have hd : d = dim y mo := by omega
      have hmo : mo = 1 ∨ mo = 2 ∨ mo = 3 ∨ mo = 4 ∨ mo = 5 ∨ mo = 6 ∨ mo = 7 ∨ mo = 8 ∨
          mo = 9 ∨ mo = 10 ∨ mo = 11 := by omega
      rcases hmo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · simp (config := {decide := true}) only [↓reduceIte, daysFrom0_split, DOY, MP, Ysh,
          dim, leap, start] at hd ⊢
        repeat' split at hd
        all_goals omega
    · have hmo : mo = 12 := by omega
      subst hmo
      have h31 : dim y 12 = 31 := by simp [dim]
      have hd : d = 31 := by omega
      subst hd
      simp (config := {decide := true}) only [↓reduceIte, daysFrom0_split, DOY, MP, Ysh,
        Nat.add_sub_cancel]
      omega

/-! ## Timestamp text -/

theorem digit?_digitChar : ∀ n, n < 10 → digit? (digitChar n) = some n := by decide

theorem digitChar_of_digit? {c : Char} {n : Nat} (h : digit? c = some n) : n < 10 ∧ digitChar n = c := by
  unfold digit? at h
  split at h
  · rename_i hd
    simp only [Option.some.injEq] at h
    subst h
    simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨h1, h2⟩ := hd
    have h1 : 48 ≤ c.toNat := h1
    have h2 : c.toNat ≤ 57 := h2
    refine ⟨by omega, ?_⟩
    unfold digitChar
    rw [show '0'.toNat + (c.toNat - 48) = c.toNat by simp; omega]
    exact Char.ofNat_toNat c
  · simp at h

theorem num2_some {a b : Char} {n : Nat} (h : num2 a b = some n) :
    n < 100 ∧ pad2 n = [a, b] := by
  unfold num2 at h
  cases ha : digit? a with
  | none => simp [ha] at h
  | some x =>
    cases hb : digit? b with
    | none => simp [ha, hb] at h
    | some y =>
      simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨hx, rfl⟩ := digitChar_of_digit? ha
      obtain ⟨hy, rfl⟩ := digitChar_of_digit? hb
      subst h
      refine ⟨by omega, ?_⟩
      simp only [pad2]
      rw [show (10 * x + y) / 10 % 10 = x by omega, show (10 * x + y) % 10 = y by omega]

theorem num4_some {a b c d : Char} {n : Nat} (h : num4 a b c d = some n) :
    n < 10000 ∧ pad4 n = [a, b, c, d] := by
  unfold num4 at h
  cases hab : num2 a b with
  | none => simp [hab] at h
  | some x =>
    cases hcd : num2 c d with
    | none => simp [hab, hcd] at h
    | some y =>
      simp only [hab, hcd, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨hx, px⟩ := num2_some hab
      obtain ⟨hy, py⟩ := num2_some hcd
      subst h
      refine ⟨by omega, ?_⟩
      simp only [pad2, List.cons.injEq] at px py
      obtain ⟨rfl, rfl, -⟩ := px
      obtain ⟨rfl, rfl, -⟩ := py
      simp only [pad4]
      rw [show (100 * x + y) / 1000 % 10 = x / 10 % 10 by omega,
        show (100 * x + y) / 100 % 10 = x % 10 by omega,
        show (100 * x + y) / 10 % 10 = y / 10 % 10 by omega,
        show (100 * x + y) % 10 = y % 10 by omega]

theorem pad2_num {n : Nat} (hn : n < 100) {a b : Char} (h : pad2 n = [a, b]) :
    num2 a b = some n := by
  simp only [pad2, List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [num2]
  rw [digit?_digitChar _ (by omega), digit?_digitChar _ (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
  omega

theorem pad4_num {n : Nat} (hn : n < 10000) {a b c d : Char} (h : pad4 n = [a, b, c, d]) :
    num4 a b c d = some n := by
  simp only [pad4, List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  simp only [num4, num2]
  rw [digit?_digitChar _ (by omega), digit?_digitChar _ (by omega),
    digit?_digitChar _ (by omega), digit?_digitChar _ (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
  omega

theorem parseTs_iso (c : Civil) (hc : c.Acceptable) : parseTs (iso c) = some (secs c) := by
  have hc' := hc
  obtain ⟨⟨⟨hy1, hm1, hm2, hd1, hd2⟩, hh, hmi, hs⟩, hy, hy2⟩ := hc'
  have hdim : dim c.y c.mo ≤ 31 := by unfold dim; split <;> (try split) <;> omega
  obtain ⟨y1, y2, y3, y4, ey⟩ : ∃ a b c' d, pad4 c.y = [a, b, c', d] := ⟨_, _, _, _, rfl⟩
  obtain ⟨m1, m2, em⟩ : ∃ a b, pad2 c.mo = [a, b] := ⟨_, _, rfl⟩
  obtain ⟨d1, d2, ed⟩ : ∃ a b, pad2 c.d = [a, b] := ⟨_, _, rfl⟩
  obtain ⟨h1, h2, eh⟩ : ∃ a b, pad2 c.h = [a, b] := ⟨_, _, rfl⟩
  obtain ⟨i1, i2, ei⟩ : ∃ a b, pad2 c.mi = [a, b] := ⟨_, _, rfl⟩
  obtain ⟨s1, s2, es⟩ : ∃ a b, pad2 c.s = [a, b] := ⟨_, _, rfl⟩
  unfold parseTs iso
  rw [String.toList_ofList]
  simp only [isoChars, ey, em, ed, eh, ei, es, List.cons_append, List.nil_append]
  rw [pad4_num (by omega) ey, pad2_num (by omega) em, pad2_num (by omega) ed,
    pad2_num (by omega) eh, pad2_num (by omega) ei, pad2_num (by omega) es]
  simp only [Option.bind_eq_bind, Option.bind_some, hc, ↓reduceIte]

theorem parseTs_some {s : String} {t : Instant} (h : parseTs s = some t) :
    ∃ c, c.Acceptable ∧ s = iso c ∧ t = secs c := by
  unfold parseTs at h
  split at h
  · rename_i y1 y2 y3 y4 m1 m2 d1 d2 h1 h2 i1 i2 s1 s2 hs
    cases ey : num4 y1 y2 y3 y4 <;> cases em : num2 m1 m2 <;> cases ed : num2 d1 d2 <;>
      cases eh : num2 h1 h2 <;> cases ei : num2 i1 i2 <;> cases es : num2 s1 s2 <;>
      simp only [ey, em, ed, eh, ei, es, Option.bind_eq_bind, Option.bind_some, Option.bind_none,
        reduceCtorEq] at h
    rename_i y mo d hh mi ss
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      refine ⟨_, hc, ?_, h.symm⟩
      apply String.ext
      rw [hs, iso, String.toList_ofList]
      simp only [isoChars, (num4_some ey).2, (num2_some em).2, (num2_some ed).2, (num2_some eh).2,
        (num2_some ei).2, (num2_some es).2, List.cons_append, List.nil_append]
    · simp at h
  · simp at h

end LakeLevel.Cal
