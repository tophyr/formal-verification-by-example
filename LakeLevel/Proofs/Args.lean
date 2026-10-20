import LakeLevel.Impl.Args
import LakeLevel.Proofs.ArgsLemmas
import LakeLevel.Proofs.Decimal

/-! # Obligations: command line and URL safety (R1, R2, R6) -/

namespace LakeLevel

private theorem site_ok : SiteSyntax "3963" := by decide
private theorem type_ok : TypeSyntax "lakelevel" := by decide
private theorem topic_ok : TopicSyntax "csarbora" := by decide

/-- Soundness: every accepted configuration is syntactically valid. -/
theorem parseArgs_sound (argv : List String) (cfg : Cfg) (h : parseArgs argv = .ok cfg) :
    CfgSound cfg := by
  unfold parseArgs at h
  split at h
  · simp at h
  · rename_i st _
    by_cases hh : st.help
    · simp [hh] at h
    · simp only [hh, Bool.false_eq_true, ite_false] at h
      obtain ⟨h1, h2, h3, h4⟩ := finalize_ok st cfg h
      refine ⟨h1, h2, h3, ?_⟩
      intro th hth
      exact (parseDec_iff th.text th.value).mp (h4 th hth)

/-- No arguments means the PRD defaults. -/
theorem parseArgs_nil : parseArgs [] = .ok defaultCfg := by decide

/-- `--site v` / `--site=v`, for **every** string `v`. -/
theorem parseArgs_site (v : String) :
    (parseArgs ["--site", v] = parseArgs ["--site=" ++ v]) ∧
    (∀ cfg, parseArgs ["--site", v] = .ok cfg ↔ SiteSyntax v ∧ cfg = { defaultCfg with site := v }) := by
  refine ⟨?_, ?_⟩
  · have := parseLoop_eqForm ("--site=" ++ v) "--site" v (by eqform_side) (by eqform_side) (by eqform_side)
      (by eqform_side) (by eqform_side) (by eqform_side) (by eqform_side)
    simp only [parseArgs, this]
  · intro cfg
    have hl : parseLoop ["--site", v] {} = .ok { site := some v } := by
      simp [parseLoop, valuedOpts, setOpt, pure, Except.pure, bind, Except.bind]
    by_cases hs : SiteSyntax v
    · simp [parseArgs, hl, finalize, hs, type_ok, topic_ok, defaultCfg, eq_comm]
    · simp [parseArgs, hl, finalize, hs, defaultCfg]

/-- `--type v` / `--type=v`, for every `v`. -/
theorem parseArgs_type (v : String) :
    (parseArgs ["--type", v] = parseArgs ["--type=" ++ v]) ∧
    (∀ cfg, parseArgs ["--type", v] = .ok cfg ↔ TypeSyntax v ∧ cfg = { defaultCfg with type := v }) := by
  refine ⟨?_, ?_⟩
  · have := parseLoop_eqForm ("--type=" ++ v) "--type" v (by eqform_side) (by eqform_side) (by eqform_side)
      (by eqform_side) (by eqform_side) (by eqform_side) (by eqform_side)
    simp only [parseArgs, this]
  · intro cfg
    have hl : parseLoop ["--type", v] {} = .ok { type := some v } := by
      simp [parseLoop, valuedOpts, setOpt, pure, Except.pure, bind, Except.bind]
    by_cases hs : TypeSyntax v
    · simp [parseArgs, hl, finalize, hs, site_ok, topic_ok, defaultCfg, eq_comm]
    · simp [parseArgs, hl, finalize, hs, defaultCfg, site_ok]

/-- `--ntfy-topic v` / `--ntfy-topic=v`, for every `v`. -/
theorem parseArgs_topic (v : String) :
    (parseArgs ["--ntfy-topic", v] = parseArgs ["--ntfy-topic=" ++ v]) ∧
    (∀ cfg, parseArgs ["--ntfy-topic", v] = .ok cfg ↔
      TopicSyntax v ∧ cfg = { defaultCfg with topic := v }) := by
  refine ⟨?_, ?_⟩
  · have := parseLoop_eqForm ("--ntfy-topic=" ++ v) "--ntfy-topic" v (by eqform_side) (by eqform_side) (by eqform_side)
      (by eqform_side) (by eqform_side) (by eqform_side) (by eqform_side)
    simp only [parseArgs, this]
  · intro cfg
    have hl : parseLoop ["--ntfy-topic", v] {} = .ok { topic := some v } := by
      simp [parseLoop, valuedOpts, setOpt, pure, Except.pure, bind, Except.bind]
    by_cases hs : TopicSyntax v
    · simp [parseArgs, hl, finalize, hs, site_ok, type_ok, defaultCfg, eq_comm]
    · simp [parseArgs, hl, finalize, hs, defaultCfg, site_ok, type_ok]

/-- `--threshold v` / `--threshold=v`, for every `v`: accepted iff `v` is a
decimal literal, and then the value is exactly what `v` denotes. -/
theorem parseArgs_threshold (v : String) :
    (parseArgs ["--threshold", v] = parseArgs ["--threshold=" ++ v]) ∧
    (∀ cfg, parseArgs ["--threshold", v] = .ok cfg ↔
      ∃ d, parseDec v = some d ∧ cfg = { defaultCfg with threshold := some ⟨v, d⟩ }) := by
  refine ⟨?_, ?_⟩
  · have := parseLoop_eqForm ("--threshold=" ++ v) "--threshold" v (by eqform_side) (by eqform_side) (by eqform_side)
      (by eqform_side) (by eqform_side) (by eqform_side) (by eqform_side)
    simp only [parseArgs, this]
  · intro cfg
    have hl : parseLoop ["--threshold", v] {} = .ok { threshold := some v } := by
      simp [parseLoop, valuedOpts, setOpt, pure, Except.pure, bind, Except.bind]
    cases hd : parseDec v with
    | none => simp [parseArgs, hl, finalize, hd, defaultCfg, site_ok, type_ok, topic_ok]
    | some d => simp [parseArgs, hl, finalize, hd, site_ok, type_ok, topic_ok, defaultCfg, eq_comm]

/-- `--json`. -/
theorem parseArgs_json : parseArgs ["--json"] = .ok { defaultCfg with json := true } := by decide

/-- Repeating an option is a usage error (A20), for every pair of values. -/
theorem parseArgs_dup (o v w : String)
    (ho : o ∈ ["--site", "--type", "--threshold", "--ntfy-topic"]) :
    ∃ m, parseArgs [o, v, o, w] = .usage m := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl <;>
    exact ⟨_, by simp [parseArgs, parseLoop, valuedOpts, setOpt]; rfl⟩

/-- URL safety (R6): after the fixed prefix, only `[0-9a-z/]`. -/
theorem fetchReq_url_safe (cfg : Cfg) (h : CfgSound cfg) :
    UrlTail hydrometPrefix (fetchReq cfg).url
      (fun c => c.isDigit ∨ ('a' ≤ c ∧ c ≤ 'z') ∨ c = '/') := by
  obtain ⟨⟨_, _, hs⟩, ⟨_, _, ht⟩, _⟩ := h
  refine ⟨cfg.site.toList ++ ['/'] ++ cfg.type.toList, ?_, ?_⟩
  · simp [fetchReq, String.toList_append]
  · intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (hc | hc) | hc
    · exact Or.inl (hs c hc)
    · exact Or.inr (Or.inr hc)
    · exact Or.inr (Or.inl (ht c hc))

/-- The request is exactly the PRD §4 request (R4). -/
theorem fetchReq_eq (cfg : Cfg) :
    fetchReq cfg = { method := "GET", url := hydrometPrefix ++ cfg.site ++ "/" ++ cfg.type,
                     headers := [("User-Agent", "lake-level/1.0")], body := "" } := rfl

end LakeLevel
