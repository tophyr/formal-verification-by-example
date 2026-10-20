import LakeLevel.Impl.Decode
import LakeLevel.Proofs.Calendar
import LakeLevel.Proofs.Decimal
import LakeLevel.Proofs.Select

/-! # Lemmas for the decoder: one characterization per validation step -/

namespace LakeLevel

open Lean (Json JsonNumber)

theorem Except.bind_ok_iff {ε α β : Type} (x : Except ε α) (f : α → Except ε β) (b : β) :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem Except.pure_ok_iff {ε α : Type} (a b : α) : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

/-- `mapM` in `Except` succeeds exactly when every element succeeds, index by index. -/
theorem mapM_except_ok_iff {α β ε : Type} (f : α → Except ε β) (l : List α) (rs : List β) :
    l.mapM f = .ok rs ↔
      rs.length = l.length ∧
      ∀ (i : Nat) (h1 : i < l.length) (h2 : i < rs.length), f l[i] = .ok rs[i] := by
  induction l generalizing rs with
  | nil => cases rs <;> simp [pure, Except.pure]
  | cons a l ih =>
    simp only [List.mapM_cons, Except.bind_ok_iff, Except.pure_ok_iff]
    constructor
    · rintro ⟨b, hb, bs, hbs, rfl⟩
      obtain ⟨hlen, hall⟩ := (ih bs).1 hbs
      refine ⟨by simp [hlen], ?_⟩
      intro i h1 h2
      cases i with
      | zero => simp only [List.getElem_cons_zero]; exact hb
      | succ i =>
        simp only [List.getElem_cons_succ]
        exact hall i (by simpa using h1) (by simpa using h2)
    · rintro ⟨hlen, hall⟩
      cases rs with
      | nil => simp at hlen
      | cons b bs =>
        have h0 := hall 0 (by simp) (by simp)
        simp only [List.getElem_cons_zero] at h0
        refine ⟨b, h0, bs, ?_, rfl⟩
        refine (ih bs).2 ⟨by simpa using hlen, ?_⟩
        intro i h1 h2
        have hi := hall (i + 1) (by simpa using h1) (by simpa using h2)
        simp only [List.getElem_cons_succ] at hi
        exact hi

theorem recDateTime_ok_iff (j : Json) (s : String) :
    recDateTime j = .ok s ↔ j.getObjVal? "dateTime" = .ok (.str s) := by
  unfold recDateTime
  split <;> simp_all

theorem recTime_ok_iff (s : String) (t : Instant) : recTime s = .ok t ↔ parseTs s = some t := by
  unfold recTime
  split <;> simp_all

theorem recValue_ok_iff (j : Json) (n : JsonNumber) :
    recValue j = .ok n ↔ j.getObjVal? "value1" = .ok (.num n) := by
  unfold recValue
  split <;> simp_all

/-- A record parses exactly when it satisfies `RecOK`. -/
theorem parseRecord_ok_iff (j : Json) (r : Reading) : parseRecord j = .ok r ↔ RecOK secs j r := by
  have hp := parseTs_spec
  unfold ParsesTimestamps at hp
  unfold parseRecord RecOK
  simp only [Except.bind_ok_iff, Except.pure_ok_iff, recDateTime_ok_iff, recTime_ok_iff,
    recValue_ok_iff, hp]
  constructor
  · rintro ⟨s, hs, t, ⟨c, hc, hsc, htc⟩, n, hn, rfl⟩
    exact ⟨⟨s, c, hs, hc, hsc, htc, rfl⟩, ⟨n, hn, rfl⟩⟩
  · rintro ⟨⟨s, c, hs, hc, hsc, htc, his⟩, ⟨n, hn, hl⟩⟩
    refine ⟨s, hs, r.t, ⟨c, hc, hsc, htc⟩, n, hn, ?_⟩
    cases r; simp_all

theorem checkHead_ok_iff (j : Json) :
    checkHead j = .ok () ↔ j.getObjVal? "value1Type" = .ok (.str "Head") := by
  unfold checkHead
  split <;> simp_all

theorem Dec.val_nat (n : Nat) : (⟨n, 0⟩ : Dec).val = (n : Rat) := by
  simp only [Dec.val, Rat.intCast_natCast, Rat.div_def, Nat.pow_zero]
  grind

theorem checkSite_ok_iff (site : Nat) (j : Json) :
    checkSite site j = .ok () ↔
      ∀ v, j.getObjVal? "siteNumber" = .ok v → ∃ n, v = .num n ∧ (Dec.ofJson n).val = (site : Rat) := by
  unfold checkSite
  cases hj : j.getObjVal? "siteNumber" with
  | error e => simp
  | ok v =>
    cases v with
    | num n =>
      simp only [Except.ok.injEq, forall_eq', Json.num.injEq, exists_eq_left']
      rw [← Dec.val_nat site]
      by_cases hc : (Dec.le (Dec.ofJson n) ⟨site, 0⟩ && Dec.le ⟨site, 0⟩ (Dec.ofJson n)) = true
      · simp only [hc, ite_true, true_iff]
        simp only [Bool.and_eq_true, Dec.le_iff] at hc
        exact Rat.le_antisymm hc.1 hc.2
      · simp only [hc, Bool.false_eq_true, ite_false, reduceCtorEq, false_iff]
        intro he
        simp only [Bool.and_eq_true, Dec.le_iff, not_and] at hc
        exact hc (he ▸ Rat.le_refl) (he ▸ Rat.le_refl)
    | _ => simp

theorem getRecords_ok_iff (j : Json) (recs : Array Json) :
    getRecords j = .ok recs ↔ j.getObjVal? "records" = .ok (.arr recs) := by
  unfold getRecords
  split <;> simp_all

theorem pickLatest_ok_iff (rs : List Reading) (r : Reading) :
    pickLatest rs = .ok r ↔ Latest rs r := by
  rw [← select_iff]
  unfold pickLatest
  split <;> simp_all

/-- `decode` succeeds exactly when every validation step does. -/
theorem decode_ok_steps (site : Nat) (j : Json) (S : Site) (R : Reading) :
    decode site j = .ok (S, R) ↔
      checkHead j = .ok () ∧ checkSite site j = .ok () ∧
      ∃ recs, getRecords j = .ok recs ∧ ∃ rs, recs.toList.mapM parseRecord = .ok rs ∧
        pickLatest rs = .ok R ∧ S = SiteOf site j := by
  unfold decode
  simp only [Except.bind_ok_iff, Except.pure_ok_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟩, h1, ⟨⟩, h2, recs, h3, rs, h4, r, h5, rfl, rfl⟩
    exact ⟨h1, h2, recs, h3, rs, h4, h5, rfl⟩
  · rintro ⟨h1, h2, recs, h3, rs, h4, h5, rfl⟩
    exact ⟨(), h1, (), h2, recs, h3, rs, h4, R, h5, rfl, rfl⟩

end LakeLevel
