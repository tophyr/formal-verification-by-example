import LakeLevel.Spec.Response
import LakeLevel.Impl.Select

/-! # Obligations: selecting the most recent reading (R20–R22) -/

namespace LakeLevel

/-- The step function of `select`'s fold. -/
private abbrev step (best x : Reading) : Reading := if best.t < x.t then x else best

/-- `Latest`, restated without indices: the list splits as `pre ++ r :: post`,
nothing in the list is later than `r`, and everything in `pre` is strictly earlier. -/
private theorem latest_of_split {rs pre post : List Reading} {r : Reading}
    (hs : rs = pre ++ r :: post) (hle : ∀ x ∈ rs, x.t ≤ r.t) (hlt : ∀ x ∈ pre, x.t < r.t) :
    Latest rs r := by
  subst hs
  refine ⟨pre.length, by simp, by simp, ?_, ?_⟩
  · intro j hj; exact hle _ (List.getElem_mem hj)
  · intro j hj
    rw [List.getElem_append_left hj]
    exact hlt _ (List.getElem_mem hj)

/-- The fold's result splits the list as `Latest` requires. -/
private theorem fold_split (l : List Reading) (r : Reading) :
    ∃ pre post, r :: l = pre ++ l.foldl step r :: post ∧
      (∀ x ∈ r :: l, x.t ≤ (l.foldl step r).t) ∧ (∀ x ∈ pre, x.t < (l.foldl step r).t) := by
  induction l generalizing r with
  | nil => exact ⟨[], [], by simp, by simp, by simp⟩
  | cons x l ih =>
    simp only [List.foldl_cons]
    obtain ⟨pre, post, hs, hle, hlt⟩ := ih (step r x)
    generalize hm : l.foldl step (step r x) = m at hs hle hlt ⊢
    by_cases h : r.t < x.t
    · have hsx : step r x = x := by simp [step, h]
      rw [hsx] at hs hle
      have hxm := hle x (by simp)
      refine ⟨r :: pre, post, by simp [hs], ?_, ?_⟩
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with hy | hy
        · subst hy; simp only [Instant] at *; omega
        · exact hle y (by simp [hy])
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with hy | hy
        · subst hy; simp only [Instant] at *; omega
        · exact hlt y hy
    · have hsx : step r x = r := by simp [step, h]
      rw [hsx] at hs hle
      have hxr : x.t ≤ r.t := by simp only [Instant] at *; omega
      have hrm := hle r (by simp)
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hs
        obtain ⟨hrm', hl⟩ := hs
        refine ⟨[], x :: l, by simp [← hrm'], ?_, by simp⟩
        intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with hy | hy | hy
        · exact hle y (by simp [hy])
        · subst hy; simp only [Instant] at *; omega
        · exact hle y (by simp [hy])
      | cons p pre' =>
        simp only [List.cons_append, List.cons.injEq] at hs
        obtain ⟨hpr, hl⟩ := hs
        have hrlt : r.t < m.t := hlt p (by simp) |> fun h' => hpr ▸ h'
        refine ⟨r :: x :: pre', post, by simp [hl], ?_, ?_⟩
        · intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with hy | hy | hy
          · exact hle y (by simp [hy])
          · subst hy; simp only [Instant] at *; omega
          · exact hle y (by simp [hy])
        · intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with hy | hy | hy
          · subst hy; exact hrlt
          · subst hy; simp only [Instant] at *; omega
          · exact hlt y (by simp [hy])

/-- `Latest` is functional: the spec picks at most one reading. -/
theorem Latest.unique {rs : List Reading} {r r' : Reading}
    (h : Latest rs r) (h' : Latest rs r') : r = r' := by
  obtain ⟨i, hi, hri, hle, hlt⟩ := h
  obtain ⟨i', hi', hri', hle', hlt'⟩ := h'
  have h1 := hle i' hi'
  have h2 := hle' i hi
  rw [hri'] at h1
  rw [hri] at h2
  rcases Nat.lt_trichotomy i i' with hc | hc | hc
  · have := hlt' i hc; simp only [hri] at this; simp only [Instant] at *; omega
  · subst hc; rw [← hri, ← hri']
  · have := hlt i' hc; simp only [hri'] at this; simp only [Instant] at *; omega

/-- `select` returns exactly the reading the spec describes. -/
theorem select_iff (rs : List Reading) (r : Reading) :
    select rs = some r ↔ Latest rs r := by
  have hsel : ∀ x l, Latest (x :: l) (l.foldl step x) := fun x l => by
    obtain ⟨pre, post, hs, hle, hlt⟩ := fold_split l x
    exact latest_of_split hs hle hlt
  constructor
  · intro h
    cases rs with
    | nil => simp [select] at h
    | cons x l =>
      simp only [select, Option.some.injEq] at h
      subst h
      exact hsel x l
  · intro h
    cases rs with
    | nil => obtain ⟨i, hi, _⟩ := h; simp at hi
    | cons x l =>
      simp only [select, Option.some.injEq]
      exact Latest.unique (hsel x l) h

/-- … and only fails on an empty list. -/
theorem select_none_iff (rs : List Reading) : select rs = none ↔ rs = [] := by
  cases rs <;> simp [select]

end LakeLevel
