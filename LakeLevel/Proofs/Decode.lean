import LakeLevel.Impl.Decode
import LakeLevel.Proofs.DecodeLemmas

/-! # Obligations: response validation (R10–R15) -/

namespace LakeLevel

open Lean (Json)

/-- The records parse to `rs` exactly when `rs` is the `RecOK` list of the spec. -/
private theorem mapM_parseRecord_iff (recs : Array Json) (rs : List Reading) :
    recs.toList.mapM parseRecord = .ok rs ↔
      rs.length = recs.size ∧
      ∀ (i : Nat) (hi : i < recs.size) (hr : i < rs.length), RecOK secs recs[i] rs[i] := by
  rw [mapM_except_ok_iff]
  simp only [Array.length_toList, Array.getElem_toList, parseRecord_ok_iff]

/-- `decode` succeeds exactly on valid responses, returning the spec's site
facts and the spec's most recent reading. -/
theorem decode_ok_iff (site : Nat) (j : Json) (S : Site) (R : Reading) :
    decode site j = .ok (S, R) ↔
      ∃ rs, ValidResp secs site j rs ∧ S = SiteOf site j ∧ Latest rs R := by
  rw [decode_ok_steps, checkHead_ok_iff, checkSite_ok_iff]
  constructor
  · rintro ⟨h1, h2, recs, h3, rs, h4, h5, hS⟩
    rw [getRecords_ok_iff] at h3
    rw [mapM_parseRecord_iff] at h4
    rw [pickLatest_ok_iff] at h5
    refine ⟨rs, ⟨h1, h2, recs, h3, ?_, h4⟩, hS, h5⟩
    -- the records are non-empty, because `Latest` found one
    obtain ⟨i, hi, _⟩ := h5
    intro hnil
    have : recs.size = 0 := by simpa using congrArg List.length hnil
    omega
  · rintro ⟨rs, ⟨h1, h2, recs, h3, _, h4⟩, hS, hL⟩
    refine ⟨h1, h2, recs, (getRecords_ok_iff j recs).2 h3, rs,
      (mapM_parseRecord_iff recs rs).2 h4, (pickLatest_ok_iff rs R).2 hL, hS⟩

/-- `decode` fails exactly on invalid responses. -/
theorem decode_error_iff (site : Nat) (j : Json) :
    (∃ m, decode site j = .error m) ↔ ¬ ∃ rs, ValidResp secs site j rs := by
  constructor
  · rintro ⟨m, hm⟩ ⟨rs, hv⟩
    -- a valid response has a non-empty reading list, hence a latest reading …
    have hne : rs ≠ [] := by
      obtain ⟨_, _, recs, _, hrecs, hlen, _⟩ := hv
      intro hnil
      apply hrecs
      have : recs.size = 0 := by simp [hnil] at hlen; omega
      simpa [List.eq_nil_iff_length_eq_zero] using this
    cases hs : select rs with
    | none => exact hne ((select_none_iff rs).1 hs)
    | some R =>
      -- … so `decode` succeeds, contradicting `hm`
      have hok := (decode_ok_iff site j (SiteOf site j) R).2 ⟨rs, hv, rfl, (select_iff rs R).1 hs⟩
      rw [hm] at hok
      cases hok
  · intro hnv
    cases hd : decode site j with
    | error m => exact ⟨m, rfl⟩
    | ok p =>
      obtain ⟨S, R⟩ := p
      obtain ⟨rs, hv, _⟩ := (decode_ok_iff site j S R).1 hd
      exact absurd ⟨rs, hv⟩ hnv

end LakeLevel
