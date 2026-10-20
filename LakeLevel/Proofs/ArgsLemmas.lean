import LakeLevel.Impl.Args

/-! # Helper lemmas for `Proofs/Args.lean` -/

namespace LakeLevel

/-- Close `s ≠ t` for strings whose character lists visibly differ
(e.g. a literal prefix `++ v` versus another literal). -/
macro "lit_ne" : tactic =>
  `(tactic| (intro h; have := congrArg String.toList h; simp [String.toList_append] at this))

/-- `--opt=v` behaves exactly like `--opt v`, given the facts about `--opt`
that make the `=`-branch of `parseLoop` the one taken. -/
theorem parseLoop_eqForm (tok o v : String) (ho : o ∈ valuedOpts)
    (hsplit : splitEq tok = some (o, v))
    (hh : tok ≠ "--help") (hj : tok ≠ "--json")
    (hv : tok ∉ valuedOpts) (hoh : o ≠ "--help") (hoj : o ≠ "--json") :
    parseLoop [tok] {} = parseLoop [o, v] {} := by
  simp [parseLoop, hh, hj, hv, hsplit, ho, hoh, hoj]

/-- Discharge the side conditions of `parseLoop_eqForm` for a literal option. -/
macro "eqform_side" : tactic =>
  `(tactic| first
    | decide
    | (simp [splitEq, String.toList_append]; done)
    | lit_ne
    | (simp only [valuedOpts, List.mem_cons, List.not_mem_nil, or_false, not_or]
       refine ⟨?_, ?_, ?_, ?_⟩ <;> lit_ne))

/-- `finalize` only ever accepts syntactically valid fields, and a threshold
whose value is what `parseDec` made of its text. -/
theorem finalize_ok (st : ArgState) (cfg : Cfg) (h : finalize st = .ok cfg) :
    SiteSyntax cfg.site ∧ TypeSyntax cfg.type ∧ TopicSyntax cfg.topic ∧
    ∀ th, cfg.threshold = some th → parseDec th.text = some th.value := by
  by_cases h1 : SiteSyntax (st.site.getD defaultCfg.site)
  · by_cases h2 : TypeSyntax (st.type.getD defaultCfg.type)
    · by_cases h3 : TopicSyntax (st.topic.getD defaultCfg.topic)
      · cases ht : st.threshold with
        | none =>
          simp only [finalize, h1, h2, h3, ht, not_true_eq_false, ite_false,
            ArgResult.ok.injEq] at h
          subst h
          exact ⟨h1, h2, h3, by intro th hth; simp at hth⟩
        | some text =>
          cases hd : parseDec text with
          | none => simp [finalize, h1, h2, h3, ht, hd] at h
          | some d =>
            simp only [finalize, h1, h2, h3, ht, hd, not_true_eq_false, ite_false,
              ArgResult.ok.injEq] at h
            subst h
            refine ⟨h1, h2, h3, ?_⟩
            intro th hth
            simp only [Option.some.injEq] at hth
            subst hth
            exact hd
      · simp [finalize, h1, h2, h3] at h
    · simp [finalize, h1, h2] at h
  · simp [finalize, h1] at h

end LakeLevel
