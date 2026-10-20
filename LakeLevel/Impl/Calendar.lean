import LakeLevel.Spec.Calendar

/-! # Impl: day numbers, instants, timestamp parsing, 12-hour clock -/

namespace LakeLevel

/-- Day number of a date, 1970-01-01 = 0. -/
def days (y mo d : Nat) : Int := sorry

/-- Seconds since the epoch of a civil time. -/
def secs (c : Civil) : Instant := sorry

/-- The earliest instant `civilOf` is specified on: 0001-01-01T00:00:00Z. -/
def minInstant : Instant := sorry

/-- The civil time of an instant. -/
def civilOf (t : Instant) : Civil := sorry

/-- Strict `YYYY-MM-DDTHH:MM:SSZ` parser. -/
def parseTs (s : String) : Option Instant := sorry

/-- 24-hour hour to 12-hour clock. -/
def hour12 (h : Nat) : Nat × Meridiem := sorry

end LakeLevel
