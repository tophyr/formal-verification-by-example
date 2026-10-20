import LakeLevel.Impl.Render

/-! # Obligations: output and alert content (R40, R51, R60) -/

namespace LakeLevel

open Lean (Json JsonNumber)

/-- Error messages are one line (A18). -/
theorem sanitize_no_newline (m : String) : '\n' ∉ (sanitize m).toList := sorry

/-- The JSON report has the A14 fields with the right values (R40). -/
theorem jsonReport_fields (S : Site) (R : Reading) :
    (jsonReport S R).getObjVal? "site" = .ok (.str S.name) ∧
    (jsonReport S R).getObjVal? "siteNumber" = .ok (.num ⟨S.number, 0⟩) ∧
    (jsonReport S R).getObjVal? "level_ft" = .ok (.num ⟨R.level.m, R.level.e⟩) ∧
    (jsonReport S R).getObjVal? "unit" = .ok (.str "Head") ∧
    (jsonReport S R).getObjVal? "observed_utc" = .ok (.str R.iso) ∧
    (jsonReport S R).getObjVal? "operating_range_max_ft" =
      .ok (match S.full with | some f => .num ⟨f.m, f.e⟩ | none => .null) := sorry

/-- The alert goes to ntfy, to a path that is exactly the topic (R6, A17). -/
theorem alertReq_url_safe (cfg : Cfg) (S : Site) (R : Reading) (h : CfgSound cfg) :
    UrlTail ntfyPrefix (alertReq cfg S R).url (fun c => c.isAlphanum ∨ c = '-' ∨ c = '_') := sorry

end LakeLevel
