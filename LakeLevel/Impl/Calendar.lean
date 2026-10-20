import LakeLevel.Spec.Calendar

/-!
# Impl: day numbers, instants, timestamp parsing, 12-hour clock

`daysFrom0`/`ofDays0` are Howard Hinnant's `days_from_civil` /
`civil_from_days` (http://howardhinnant.github.io/date_algorithms.html),
restricted to naturals. Day 0 is 0000-03-01, so leap days fall at the *end*
of each shifted year, and only divisions by constants appear.
-/

namespace LakeLevel

/-- Days since 0000-03-01 (valid for year ≥ 1). -/
def daysFrom0 (y mo d : Nat) : Nat :=
  let y' := if mo ≤ 2 then y - 1 else y
  let era := y' / 400
  let yoe := y' % 400                                   -- year of era, [0, 399]
  let mp := if mo > 2 then mo - 3 else mo + 9           -- March = 0, [0, 11]
  let doy := (153 * mp + 2) / 5 + d - 1                 -- day of year, [0, 365]
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy      -- day of era, [0, 146096]
  era * 146097 + doe

/-- Inverse of `daysFrom0`. -/
def ofDays0 (z : Nat) : Nat × Nat × Nat :=
  let era := z / 146097
  let doe := z % 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let mo := if mp < 10 then mp + 3 else mp - 9
  let y := yoe + era * 400
  (if mo ≤ 2 then y + 1 else y, mo, d)

/-- `daysFrom0 1970 1 1`. -/
def epochDay0 : Nat := 719468

/-- Day number of a date, 1970-01-01 = 0. -/
def days (y mo d : Nat) : Int := (daysFrom0 y mo d : Int) - epochDay0

/-- Seconds since the epoch of a civil time. -/
def secs (c : Civil) : Instant :=
  86400 * days c.y c.mo c.d + 3600 * c.h + 60 * c.mi + c.s

/-- 0001-01-01T00:00:00Z. -/
def minInstant : Instant := secs ⟨1, 1, 1, 0, 0, 0⟩

/-- The civil time of an instant (meaningful for `t ≥ minInstant`). -/
def civilOf (t : Instant) : Civil :=
  let n := (t + 86400 * epochDay0).toNat           -- seconds since 0000-03-01
  let (y, mo, d) := ofDays0 (n / 86400)
  let sod := n % 86400
  ⟨y, mo, d, sod / 3600, sod % 3600 / 60, sod % 60⟩

def digit? (c : Char) : Option Nat := if c.isDigit then some (c.toNat - 48) else none

def num2 (a b : Char) : Option Nat := do
  pure (10 * (← digit? a) + (← digit? b))

def num4 (a b c d : Char) : Option Nat := do
  pure (100 * (← num2 a b) + (← num2 c d))

/-- Strict `YYYY-MM-DDTHH:MM:SSZ` parser. -/
def parseTs (s : String) : Option Instant :=
  match s.toList with
  | [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, 'T', h1, h2, ':', i1, i2, ':', s1, s2, 'Z'] => do
    let c : Civil :=
      ⟨← num4 y1 y2 y3 y4, ← num2 m1 m2, ← num2 d1 d2, ← num2 h1 h2, ← num2 i1 i2, ← num2 s1 s2⟩
    if c.Acceptable then some (secs c) else none
  | _ => none

/-- 24-hour hour to 12-hour clock. -/
def hour12 (h : Nat) : Nat × Meridiem :=
  if h = 0 then (12, .am)
  else if h < 12 then (h, .am)
  else if h = 12 then (12, .pm)
  else (h - 12, .pm)

end LakeLevel
