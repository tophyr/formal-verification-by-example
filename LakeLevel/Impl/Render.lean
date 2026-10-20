import Lean.Data.Json
import LakeLevel.Impl.Decimal
import LakeLevel.Impl.Calendar
import LakeLevel.Spec.Args

/-! # Impl: every byte the program prints or sends -/

namespace LakeLevel

open Lean (Json)

/-- The human-readable report (R30). -/
def humanReport (S : Site) (R : Reading) (z : Zone) (now : Instant) : String := sorry

/-- The JSON report value (R40). -/
def jsonReport (S : Site) (R : Reading) : Json := sorry

/-- The JSON report text. -/
def jsonText (S : Site) (R : Reading) : String := sorry

/-- The ntfy POST (R51). -/
def alertReq (cfg : Cfg) (S : Site) (R : Reading) : Request := sorry

/-- Replace newlines so an error message is one line (A18). -/
def sanitize (m : String) : String := sorry

/-- `Error: {m}\n` (R60). -/
def errLine (m : String) : String := sorry

/-- The stderr note after a delivered alert (R53). -/
def alertNotice (cfg : Cfg) : String := sorry

def usageText : String := sorry
def helpText : String := sorry

end LakeLevel
