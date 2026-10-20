import LakeLevel.Spec.Calendar
import LakeLevel.Impl.Calendar
import LakeLevel.Proofs.CalendarLemmas

/-! # Obligations: calendar, instants, timestamps, clock (R23, R33, R34, R41, A2) -/

namespace LakeLevel

/-- `days` is *the* day count: it satisfies the characterization. -/
theorem days_spec : DayCount days := by
  refine ⟨by decide, ?_⟩
  intro y mo d h
  have := Cal.daysFrom0_next h
  rcases hn : nextDate y mo d with ⟨y', mo', d'⟩
  rw [hn] at this
  dsimp only at this
  simp only [days]
  omega

/-- Distinct valid civil times are distinct instants. -/
theorem secs_injective {c c' : Civil} (hc : c.Valid) (hc' : c'.Valid)
    (h : secs c = secs c') : c = c' := by
  obtain ⟨y, mo, d, hh, mi, ss⟩ := c
  obtain ⟨y', mo', d', hh', mi', ss'⟩ := c'
  obtain ⟨hv, h1, h2, h3⟩ := hc
  obtain ⟨hv', h1', h2', h3'⟩ := hc'
  simp only [secs, days] at h h1 h2 h3 h1' h2' h3' hv hv'
  have h : (_ : Int) = _ := h
  have hd : daysFrom0 y mo d = daysFrom0 y' mo' d' := by omega
  have e := Cal.ofDays0_daysFrom0 hv
  rw [hd, Cal.ofDays0_daysFrom0 hv'] at e
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  simp only [Civil.mk.injEq, true_and]
  omega

/-- `secs`, with its arithmetic at type `Int` (which `omega` recognizes) rather than `Instant`. -/
theorem secs_int (c : Civil) :
    secs c = (86400 * ((daysFrom0 c.y c.mo c.d : Int) - 719468) + 3600 * (c.h : Int) +
      60 * (c.mi : Int) + (c.s : Int) : Int) := rfl

theorem minInstant_eq : minInstant = 86400 * (306 - 719468) := by decide

/-- `civilOf`, unfolded: the date part is `ofDays0` of the day count since 0000-03-01. -/
theorem civilOf_eq (t : Instant) :
    civilOf t = ⟨(ofDays0 ((t + 86400 * 719468).toNat / 86400)).1,
      (ofDays0 ((t + 86400 * 719468).toNat / 86400)).2.1,
      (ofDays0 ((t + 86400 * 719468).toNat / 86400)).2.2,
      (t + 86400 * 719468).toNat % 86400 / 3600, (t + 86400 * 719468).toNat % 86400 % 3600 / 60,
      (t + 86400 * 719468).toNat % 86400 % 60⟩ := by
  simp only [civilOf, epochDay0]
  rfl

/-- `civilOf` always produces a real civil time … -/
theorem civilOf_valid (t : Instant) (ht : minInstant ≤ t) : (civilOf t).Valid := by
  rw [minInstant_eq] at ht
  have ht : (_ : Int) ≤ _ := ht
  rw [civilOf_eq]
  dsimp only [Civil.Valid]
  have hn : 306 ≤ (t + 86400 * 719468).toNat / 86400 := by omega
  exact ⟨(Cal.ofDays0_valid_inv _ hn).1, by omega, by omega, by omega⟩

/-- … that denotes the instant it was given. With `secs_injective`, this makes
`civilOf t` *the* civil time of `t`. -/
theorem secs_civilOf (t : Instant) (ht : minInstant ≤ t) : secs (civilOf t) = t := by
  rw [minInstant_eq] at ht
  have ht : (_ : Int) ≤ _ := ht
  have hn : 306 ≤ (t + 86400 * 719468).toNat / 86400 := by omega
  have e := (Cal.ofDays0_valid_inv _ hn).2
  rw [civilOf_eq, secs_int]
  dsimp only
  rw [e]
  have hnn : ((t + 86400 * 719468).toNat : Int) = t + 86400 * 719468 :=
    Int.toNat_of_nonneg (by omega)
  generalize (t + 86400 * 719468).toNat = n at hnn ⊢
  show (_ : Int) = _
  omega

/-- The parser accepts exactly canonical acceptable timestamps (A2, R14). -/
theorem parseTs_spec : ParsesTimestamps parseTs secs := by
  intro s t
  constructor
  · exact Cal.parseTs_some
  · rintro ⟨c, hc, rfl, rfl⟩
    exact Cal.parseTs_iso c hc

/-- Round trip (R41): re-rendering a parsed timestamp gives back the input. -/
theorem iso_civilOf_parseTs (s : String) (t : Instant) (h : parseTs s = some t) :
    iso (civilOf t) = s := by
  obtain ⟨c, hc, rfl, rfl⟩ := Cal.parseTs_some h
  have hmin : minInstant ≤ secs c := by
    have := Cal.daysFrom0_ge hc.1.1
    rw [minInstant_eq, secs_int]
    show (_ : Int) ≤ _
    omega
  rw [secs_injective (civilOf_valid _ hmin) hc.1 (secs_civilOf _ hmin)]

/-- The 12-hour clock is in range and means what it says (R33) … -/
theorem hour12_correct (h : Nat) (hh : h < 24) :
    1 ≤ (hour12 h).1 ∧ (hour12 h).1 ≤ 12 ∧ from12 (hour12 h).1 (hour12 h).2 = h := by
  revert h; decide

/-- … and every 12-hour reading is reached. -/
theorem hour12_surjective (hh : Nat) (p : Meridiem) (h1 : 1 ≤ hh) (h2 : hh ≤ 12) :
    ∃ h, h < 24 ∧ hour12 h = (hh, p) := by
  have key : ∀ k, k < 13 → 1 ≤ k →
      hour12 (if k = 12 then 0 else k) = (k, .am) ∧ hour12 (if k = 12 then 12 else k + 12) = (k, .pm) := by
    decide
  cases p
  · exact ⟨if hh = 12 then 0 else hh, by split <;> omega, (key hh (by omega) h1).1⟩
  · exact ⟨if hh = 12 then 12 else hh + 12, by split <;> omega, (key hh (by omega) h1).2⟩

end LakeLevel
