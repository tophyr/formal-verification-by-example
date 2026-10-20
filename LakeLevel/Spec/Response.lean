import Lean.Data.Json
import LakeLevel.Spec.Decimal
import LakeLevel.Spec.Calendar

/-!
# Spec: what a valid response is, and which reading is "the most recent"

docs/02-formal-model.md §2.3–2.4.

These predicates are parameterized by `secs : Civil → Instant` rather than
importing the implementation, so the spec layer never depends on the code it
constrains.
-/

namespace LakeLevel

open Lean (Json JsonNumber)

/-- A `JsonNumber` is already an exact decimal. -/
def Dec.ofJson (n : JsonNumber) : Dec := ⟨n.mantissa, n.exponent⟩

/-- **"The most recent reading"**, declaratively, over list indices (A1, R20–R22):
`r` is at some index `i`; no reading is later than `r`; and every reading
*before* index `i` is strictly earlier (so `r` is the first of the latest). -/
def Latest (rs : List Reading) (r : Reading) : Prop :=
  ∃ (i : Nat) (hi : i < rs.length),
    rs[i] = r ∧
    (∀ (j : Nat) (hj : j < rs.length), rs[j].t ≤ r.t) ∧
    (∀ (j : Nat) (hj : j < i), (rs[j]'(Nat.lt_trans hj hi)).t < r.t)

/-- JSON record `j` is well-formed and denotes reading `r` (A2, A7, R14). -/
def RecOK (secs : Civil → Instant) (j : Json) (r : Reading) : Prop :=
  (∃ (s : String) (c : Civil),
      j.getObjVal? "dateTime" = .ok (.str s) ∧
      c.Acceptable ∧ s = iso c ∧ r.t = secs c ∧ r.iso = s) ∧
  (∃ n : JsonNumber,
      j.getObjVal? "value1" = .ok (.num n) ∧ r.level = Dec.ofJson n)

/-- **A valid response** (R10–R14), and the readings `rs` it denotes, in order. -/
def ValidResp (secs : Civil → Instant) (site : Nat) (j : Json) (rs : List Reading) : Prop :=
  j.getObjVal? "value1Type" = .ok (.str "Head") ∧
  (∀ v, j.getObjVal? "siteNumber" = .ok v →
      ∃ n, v = .num n ∧ (Dec.ofJson n).val = (site : Rat)) ∧
  (∃ recs : Array Json,
      j.getObjVal? "records" = .ok (.arr recs) ∧
      recs.toList ≠ [] ∧
      rs.length = recs.size ∧
      ∀ (i : Nat) (hi : i < recs.size) (hr : i < rs.length), RecOK secs recs[i] rs[i])

/-- Site facts extracted from a response (template; A10, A13). -/
def SiteOf (site : Nat) (j : Json) : Site where
  number := site
  name := match j.getObjVal? "siteName" with
    | .ok (.str s) => s
    | _ => "site " ++ toString site
  full := match j.getObjVal? "lakeOperatingRangeMax" with
    | .ok (.num n) => some (Dec.ofJson n)
    | _ => none

end LakeLevel
