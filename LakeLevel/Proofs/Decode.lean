import LakeLevel.Impl.Decode

/-! # Obligations: response validation (R10–R15) -/

namespace LakeLevel

open Lean (Json)

/-- `decode` succeeds exactly on valid responses, returning the spec's site
facts and the spec's most recent reading. -/
theorem decode_ok_iff (site : Nat) (j : Json) (S : Site) (R : Reading) :
    decode site j = .ok (S, R) ↔
      ∃ rs, ValidResp secs site j rs ∧ S = SiteOf site j ∧ Latest rs R := sorry

/-- `decode` fails exactly on invalid responses. -/
theorem decode_error_iff (site : Nat) (j : Json) :
    (∃ m, decode site j = .error m) ↔ ¬ ∃ rs, ValidResp secs site j rs := sorry

end LakeLevel
