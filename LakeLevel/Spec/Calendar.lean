import LakeLevel.Spec.Decimal

/-!
# Spec: the calendar, timestamps, 12-hour clock

docs/02-formal-model.md §2.2. The day count is specified by
**characterization** (`DayCount`): two equations that only one function
satisfies. The implementation uses a closed-form formula that looks nothing
like them; Stage 5 bridges the gap.
-/

namespace LakeLevel

/-- Gregorian leap year. -/
def leap (y : Nat) : Prop := y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0)

instance (y : Nat) : Decidable (leap y) := by unfold leap; infer_instance

/-- Days in month `mo` of year `y`. -/
def dim (y mo : Nat) : Nat :=
  if mo = 2 then (if leap y then 29 else 28)
  else if mo = 4 ∨ mo = 6 ∨ mo = 9 ∨ mo = 11 then 30
  else 31

/-- A real calendar date (proleptic Gregorian, year ≥ 1). -/
def ValidDate (y mo d : Nat) : Prop :=
  1 ≤ y ∧ 1 ≤ mo ∧ mo ≤ 12 ∧ 1 ≤ d ∧ d ≤ dim y mo

/-- A real civil time. No leap seconds. -/
def Civil.Valid (c : Civil) : Prop :=
  ValidDate c.y c.mo c.d ∧ c.h < 24 ∧ c.mi < 60 ∧ c.s < 60

instance (y mo d : Nat) : Decidable (ValidDate y mo d) := by unfold ValidDate; infer_instance
instance (c : Civil) : Decidable c.Valid := by unfold Civil.Valid; infer_instance

/-- "Tomorrow": the obvious successor of a date. -/
def nextDate (y mo d : Nat) : Nat × Nat × Nat :=
  if d < dim y mo then (y, mo, d + 1)
  else if mo < 12 then (y, mo + 1, 1)
  else (y + 1, 1, 1)

/-- **The day count, by characterization** (R23): `f` numbers days so that
1970-01-01 is day 0 and every valid date's successor is one more.
Any two such functions agree on every valid date. -/
def DayCount (f : Nat → Nat → Nat → Int) : Prop :=
  f 1970 1 1 = 0 ∧
  ∀ y mo d, ValidDate y mo d →
    let (y', mo', d') := nextDate y mo d
    f y' mo' d' = f y mo d + 1

/-- Zero-padded, fixed-width decimal (template). -/
def pad2 (n : Nat) : List Char := [digitChar (n / 10 % 10), digitChar (n % 10)]
def pad4 (n : Nat) : List Char :=
  [digitChar (n / 1000 % 10), digitChar (n / 100 % 10), digitChar (n / 10 % 10), digitChar (n % 10)]

/-- The canonical timestamp text `YYYY-MM-DDTHH:MM:SSZ` (template, A2). -/
def isoChars (c : Civil) : List Char :=
  pad4 c.y ++ ['-'] ++ pad2 c.mo ++ ['-'] ++ pad2 c.d ++ ['T'] ++
  pad2 c.h ++ [':'] ++ pad2 c.mi ++ [':'] ++ pad2 c.s ++ ['Z']

def iso (c : Civil) : String := String.ofList (isoChars c)

/-- A timestamp the API may send: valid, 1970 ≤ year ≤ 9999 (A2). -/
def Civil.Acceptable (c : Civil) : Prop := c.Valid ∧ 1970 ≤ c.y ∧ c.y ≤ 9999

instance (c : Civil) : Decidable c.Acceptable := by unfold Civil.Acceptable; infer_instance

/-- **What the timestamp parser must do**, in one equation (A2, R14, R41):
it accepts exactly the canonical renderings of acceptable civil times, and
returns the instant `secs` assigns them. -/
def ParsesTimestamps (parse : String → Option Instant) (secs : Civil → Instant) : Prop :=
  ∀ s t, parse s = some t ↔ ∃ c, c.Acceptable ∧ s = iso c ∧ t = secs c

/-- AM/PM. -/
inductive Meridiem where
  | am | pm
  deriving Repr, DecidableEq

/-- The intended meaning of a 12-hour reading, as a 24-hour hour (R33).
Note `12 AM` is midnight. -/
def from12 (hh : Nat) (p : Meridiem) : Nat :=
  (hh % 12) + (match p with | .am => 0 | .pm => 12)

end LakeLevel
