import LakeLevel.Spec.Calendar
import LakeLevel.Impl.Calendar

/-! # Obligations: calendar, instants, timestamps, clock (R23, R33, R34, R41, A2) -/

namespace LakeLevel

/-- `days` is *the* day count: it satisfies the characterization. -/
theorem days_spec : DayCount days := sorry

/-- Distinct valid civil times are distinct instants. -/
theorem secs_injective {c c' : Civil} (hc : c.Valid) (hc' : c'.Valid)
    (h : secs c = secs c') : c = c' := sorry

/-- `civilOf` always produces a real civil time … -/
theorem civilOf_valid (t : Instant) (ht : minInstant ≤ t) : (civilOf t).Valid := sorry

/-- … that denotes the instant it was given. With `secs_injective`, this makes
`civilOf t` *the* civil time of `t`. -/
theorem secs_civilOf (t : Instant) (ht : minInstant ≤ t) : secs (civilOf t) = t := sorry

/-- The parser accepts exactly canonical acceptable timestamps (A2, R14). -/
theorem parseTs_spec : ParsesTimestamps parseTs secs := sorry

/-- Round trip (R41): re-rendering a parsed timestamp gives back the input. -/
theorem iso_civilOf_parseTs (s : String) (t : Instant) (h : parseTs s = some t) :
    iso (civilOf t) = s := sorry

/-- The 12-hour clock is in range and means what it says (R33) … -/
theorem hour12_correct (h : Nat) (hh : h < 24) :
    1 ≤ (hour12 h).1 ∧ (hour12 h).1 ≤ 12 ∧ from12 (hour12 h).1 (hour12 h).2 = h := sorry

/-- … and every 12-hour reading is reached. -/
theorem hour12_surjective (hh : Nat) (p : Meridiem) (h1 : 1 ≤ hh) (h2 : hh ≤ 12) :
    ∃ h, h < 24 ∧ hour12 h = (hh, p) := sorry

end LakeLevel
