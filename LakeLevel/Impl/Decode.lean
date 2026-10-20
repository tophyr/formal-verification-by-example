import Lean.Data.Json
import LakeLevel.Spec.Response
import LakeLevel.Impl.Calendar
import LakeLevel.Impl.Select

/-! # Impl: validate and decode an API response -/

namespace LakeLevel

open Lean (Json)

/-- Validate a decoded JSON response for `site`, and pick its most recent reading. -/
def decode (site : Nat) (j : Json) : Except String (Site × Reading) := sorry

/-- Parse the body text, then `decode`. `Json.parse` is trusted (docs/02 §2.8). -/
def decodeBody (site : Nat) (body : String) : Except String (Site × Reading) := sorry

end LakeLevel
