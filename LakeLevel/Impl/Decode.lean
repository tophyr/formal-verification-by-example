import Lean.Data.Json
import LakeLevel.Spec.Response
import LakeLevel.Impl.Decimal
import LakeLevel.Impl.Calendar
import LakeLevel.Impl.Select

/-! # Impl: validate and decode an API response -/

namespace LakeLevel

open Lean (Json)

/-! Each validation step is its own small function, so that each can be
characterized by its own lemma in `Proofs/Decode.lean`. -/

/-- A record's `dateTime` string. -/
def recDateTime (j : Json) : Except String String :=
  match j.getObjVal? "dateTime" with
  | .ok (.str s) => .ok s
  | _ => .error "a record has no dateTime string"

/-- The instant a timestamp string denotes. -/
def recTime (s : String) : Except String Instant :=
  match parseTs s with
  | some t => .ok t
  | none => .error s!"a record has an invalid timestamp: {s}"

/-- A record's numeric `value1`. -/
def recValue (j : Json) : Except String Lean.JsonNumber :=
  match j.getObjVal? "value1" with
  | .ok (.num n) => .ok n
  | _ => .error "a record has no numeric value1"

/-- One record → one reading, or an error (A7: strict). -/
def parseRecord (j : Json) : Except String Reading := do
  let s ← recDateTime j
  let t ← recTime s
  let n ← recValue j
  pure ⟨t, Dec.ofJson n, s⟩

/-- `value1Type` must be `"Head"` (A9). -/
def checkHead (j : Json) : Except String Unit :=
  match j.getObjVal? "value1Type" with
  | .ok (.str "Head") => .ok ()
  | _ => .error "response is not lake-level (Head) data"

/-- If present, `siteNumber` must equal the requested site (A10). -/
def checkSite (site : Nat) (j : Json) : Except String Unit :=
  match j.getObjVal? "siteNumber" with
  | .ok (.num n) =>
    if Dec.le (Dec.ofJson n) ⟨site, 0⟩ && Dec.le ⟨site, 0⟩ (Dec.ofJson n) then .ok ()
    else .error s!"response is for a different site than {site}"
  | .ok _ => .error "response siteNumber is not a number"
  | .error _ => .ok ()

/-- The `records` array (A8). -/
def getRecords (j : Json) : Except String (Array Json) :=
  match j.getObjVal? "records" with
  | .ok (.arr a) => .ok a
  | _ => .error "response has no records array"

/-- The most recent reading, or an error for an empty list. -/
def pickLatest (rs : List Reading) : Except String Reading :=
  match select rs with
  | some r => .ok r
  | none => .error "API returned no records"

/-- Validate a decoded JSON response for `site`, and pick its most recent reading. -/
def decode (site : Nat) (j : Json) : Except String (Site × Reading) := do
  checkHead j
  checkSite site j
  let recs ← getRecords j
  let rs ← recs.toList.mapM parseRecord
  let r ← pickLatest rs
  pure (SiteOf site j, r)

/-- Parse the body text, then `decode`. `Json.parse` is trusted (docs/02 §2.8). -/
def decodeBody (site : Nat) (body : String) : Except String (Site × Reading) :=
  match Json.parse body with
  | .ok j => decode site j
  | .error e => .error s!"response is not valid JSON: {e}"

end LakeLevel
