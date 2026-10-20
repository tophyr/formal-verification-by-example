import LakeLevel.Impl.Args

/-! # Obligations: command line and URL safety (R1, R2, R6) -/

namespace LakeLevel

/-- Soundness: every accepted configuration is syntactically valid. -/
theorem parseArgs_sound (argv : List String) (cfg : Cfg) (h : parseArgs argv = .ok cfg) :
    CfgSound cfg := sorry

/-- No arguments means the PRD defaults. -/
theorem parseArgs_nil : parseArgs [] = .ok defaultCfg := sorry

/-- `--site v` / `--site=v`, for **every** string `v`. -/
theorem parseArgs_site (v : String) :
    (parseArgs ["--site", v] = parseArgs ["--site=" ++ v]) ∧
    (∀ cfg, parseArgs ["--site", v] = .ok cfg ↔ SiteSyntax v ∧ cfg = { defaultCfg with site := v }) := sorry

/-- `--type v` / `--type=v`, for every `v`. -/
theorem parseArgs_type (v : String) :
    (parseArgs ["--type", v] = parseArgs ["--type=" ++ v]) ∧
    (∀ cfg, parseArgs ["--type", v] = .ok cfg ↔ TypeSyntax v ∧ cfg = { defaultCfg with type := v }) := sorry

/-- `--ntfy-topic v` / `--ntfy-topic=v`, for every `v`. -/
theorem parseArgs_topic (v : String) :
    (parseArgs ["--ntfy-topic", v] = parseArgs ["--ntfy-topic=" ++ v]) ∧
    (∀ cfg, parseArgs ["--ntfy-topic", v] = .ok cfg ↔
      TopicSyntax v ∧ cfg = { defaultCfg with topic := v }) := sorry

/-- `--threshold v` / `--threshold=v`, for every `v`: accepted iff `v` is a
decimal literal, and then the value is exactly what `v` denotes. -/
theorem parseArgs_threshold (v : String) :
    (parseArgs ["--threshold", v] = parseArgs ["--threshold=" ++ v]) ∧
    (∀ cfg, parseArgs ["--threshold", v] = .ok cfg ↔
      ∃ d, parseDec v = some d ∧ cfg = { defaultCfg with threshold := some ⟨v, d⟩ }) := sorry

/-- `--json`. -/
theorem parseArgs_json : parseArgs ["--json"] = .ok { defaultCfg with json := true } := sorry

/-- Repeating an option is a usage error (A20), for every pair of values. -/
theorem parseArgs_dup (o v w : String)
    (ho : o ∈ ["--site", "--type", "--threshold", "--ntfy-topic"]) :
    ∃ m, parseArgs [o, v, o, w] = .usage m := sorry

/-- URL safety (R6): after the fixed prefix, only `[0-9a-z/]`. -/
theorem fetchReq_url_safe (cfg : Cfg) (h : CfgSound cfg) :
    UrlTail hydrometPrefix (fetchReq cfg).url
      (fun c => c.isDigit ∨ ('a' ≤ c ∧ c ≤ 'z') ∨ c = '/') := sorry

/-- The request is exactly the PRD §4 request (R4). -/
theorem fetchReq_eq (cfg : Cfg) :
    fetchReq cfg = { method := "GET", url := hydrometPrefix ++ cfg.site ++ "/" ++ cfg.type,
                     headers := [("User-Agent", "lake-level/1.0")], body := "" } := sorry

end LakeLevel
