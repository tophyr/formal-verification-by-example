import Lean.Data.Json
import LakeLevel.Spec.Response
import LakeLevel.Impl.Decimal
import LakeLevel.Impl.Calendar
import LakeLevel.Impl.Select

/-! # Impl: validate and decode an API response -/

namespace LakeLevel

open Lean (Json)

/-- One record → one reading, or an error (A7: strict). -/
def parseRecord (j : Json) : Except String Reading := do
  let s ← match j.getObjVal? "dateTime" with
    | .ok (.str s) => pure s
    | _ => throw "a record has no dateTime string"
  let t ← match parseTs s with
    | some t => pure t
    | none => throw s!"a record has an invalid timestamp: {s}"
  let n ← match j.getObjVal? "value1" with
    | .ok (.num n) => pure n
    | _ => throw "a record has no numeric value1"
  pure ⟨t, Dec.ofJson n, s⟩

/-- Validate a decoded JSON response for `site`, and pick its most recent reading. -/
def decode (site : Nat) (j : Json) : Except String (Site × Reading) := do
  match j.getObjVal? "value1Type" with
  | .ok (.str "Head") => pure ()
  | _ => throw "response is not lake-level (Head) data"
  match j.getObjVal? "siteNumber" with
  | .ok (.num n) =>
    unless Dec.le (Dec.ofJson n) ⟨site, 0⟩ && Dec.le ⟨site, 0⟩ (Dec.ofJson n) do
      throw s!"response is for a different site than {site}"
  | .ok _ => throw "response siteNumber is not a number"
  | .error _ => pure ()
  let recs ← match j.getObjVal? "records" with
    | .ok (.arr a) => pure a
    | _ => throw "response has no records array"
  let rs ← recs.toList.mapM parseRecord
  match select rs with
  | some r => pure (SiteOf site j, r)
  | none => throw "API returned no records"

/-- Parse the body text, then `decode`. `Json.parse` is trusted (docs/02 §2.8). -/
def decodeBody (site : Nat) (body : String) : Except String (Site × Reading) :=
  match Json.parse body with
  | .ok j => decode site j
  | .error e => .error s!"response is not valid JSON: {e}"

end LakeLevel
