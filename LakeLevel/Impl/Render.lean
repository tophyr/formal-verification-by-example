import Lean.Data.Json
import LakeLevel.Impl.Decimal
import LakeLevel.Impl.Calendar
import LakeLevel.Spec.Args

/-! # Impl: every byte the program prints or sends -/

namespace LakeLevel

open Lean (Json)

def Meridiem.text : Meridiem → String
  | .am => "AM"
  | .pm => "PM"

/-- `YYYY-MM-DD hh:MM AM` (A11). Seconds are dropped, not rounded. -/
def clock12 (c : Civil) : String :=
  let (hh, p) := hour12 c.h
  String.ofList (pad4 c.y ++ ['-'] ++ pad2 c.mo ++ ['-'] ++ pad2 c.d ++ [' '] ++
    pad2 hh ++ [':'] ++ pad2 c.mi) ++ " " ++ p.text

/-- `N min ago` / `N min in the future` (A12). -/
def ageText (a : Int) : String :=
  if 0 ≤ a then fixed 0 a ++ " min ago" else fixed 0 (-a) ++ " min in the future"

/-- The human-readable report (R30). -/
def humanReport (S : Site) (R : Reading) (z : Zone) (now : Instant) : String :=
  let level := fixed 2 (R.level.round 2)
  let age := roundFrac (now - R.t) 60
  S.name ++ "\n" ++
  "  Most recent lake level: " ++ level ++ " ft (MSL)\n" ++
  "  Observed: " ++ clock12 (civilOf (R.t + z.offset)) ++ " " ++ z.abbr ++
    " (" ++ ageText age ++ ")\n" ++
  match S.full with
  | some F => "  Full pool: " ++ fixed 1 (F.round 1) ++ " ft  (" ++
      signed 2 ((F.sub R.level).round 2) ++ " ft from full)\n"
  | none => ""

/-- The JSON report value (R40). -/
def jsonReport (S : Site) (R : Reading) : Json :=
  Json.mkObj [
    ("site", .str S.name),
    ("siteNumber", .num ⟨S.number, 0⟩),
    ("level_ft", .num ⟨R.level.m, R.level.e⟩),
    ("unit", .str "Head"),
    ("observed_utc", .str R.iso),
    ("operating_range_max_ft", match S.full with | some f => .num ⟨f.m, f.e⟩ | none => .null)]

/-- The JSON report text. Lean's printer is trusted (docs/02 §2.8). -/
def jsonText (S : Site) (R : Reading) : String := (jsonReport S R).pretty ++ "\n"

/-- The ntfy POST (R51). The site name goes only in the body, never a header. -/
def alertReq (cfg : Cfg) (S : Site) (R : Reading) : Request :=
  let level := fixed 2 (R.level.round 2)
  { method := "POST", url := ntfyPrefix ++ cfg.topic,
    headers := [("Title", "Lake level alert: " ++ level ++ " ft"),
                ("Priority", "high"), ("Tags", "warning,ocean")],
    body := S.name ++ " lake level is " ++ level ++ " ft (MSL) as of " ++ R.iso ++
      ".\nLevel has reached the alert threshold." }

/-- Replace line breaks so an error message is one line (A18). -/
def sanitize (m : String) : String :=
  String.ofList (m.toList.map fun c => if c = '\n' ∨ c = '\r' then ' ' else c)

/-- `Error: {m}\n` (R60). Callers pass `sanitize`d text. -/
def errLine (m : String) : String := "Error: " ++ m ++ "\n"

/-- The stderr note after a delivered alert (R53). -/
def alertNotice (cfg : Cfg) : String :=
  match cfg.threshold with
  | some th => "  ALERT: level >= " ++ th.text ++ " ft -> notified ntfy.sh/" ++ cfg.topic ++ "\n"
  | none => ""

def usageText : String :=
  "usage: lake-level [--site N] [--type T] [--json] [--threshold FT] [--ntfy-topic TOPIC]\n"

def helpText : String :=
  usageText ++ "
Report the most recent LCRA lake level for a hydromet site.

options:
  --site N            LCRA site number, 1-9 digits (default: 3963, Lake Travis)
  --type T            API data type, lowercase letters (default: lakelevel)
  --json              emit machine-readable JSON
  --threshold FT      POST an ntfy.sh alert when level >= FT (decimal, e.g. 685 or 680.5)
  --ntfy-topic TOPIC  ntfy.sh topic for alerts (default: csarbora)
  --help              show this help

exit status: 0 ok, 1 runtime error (including a failed alert), 2 usage error
"

end LakeLevel
