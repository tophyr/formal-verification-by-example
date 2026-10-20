import LakeLevel.Impl.Program

/-!
# Obligations: whole-program properties, over **every** world (docs/02 §2.7)

These are the theorems the PRD actually cares about. Each is quantified over
all argument lists and all worlds: every possible network response, clock
reading, time zone, and ntfy outcome.
-/

namespace LakeLevel

def trace (argv : List String) (w : World) : List Event := ((main argv).run w).1
def exitCode (argv : List String) (w : World) : Nat := ((main argv).run w).2

/-- The world returned a successful, valid response for `cfg`, decoding to `S`, `R`. -/
def Fetched (cfg : Cfg) (w : World) (S : Site) (R : Reading) : Prop :=
  ∃ status body, w.get (fetchReq cfg) = .response status body ∧ ok2xx status ∧
    decodeBody (siteNum cfg.site) body = .ok (S, R)

/-- The alert condition (R50): a threshold was given and the exact level meets it. -/
def ShouldAlert (cfg : Cfg) (R : Reading) : Prop :=
  ∃ th, cfg.threshold = some th ∧ th.value.val ≤ R.level.val

/-- What stdout should be for a successful fetch (R30, R40). -/
def reportFor (cfg : Cfg) (w : World) (S : Site) (R : Reading) : String :=
  if cfg.json then jsonText S R else humanReport S R (w.zone R.t) w.now

/-- `--help` prints help and exits 0, touching nothing else. -/
theorem help_behavior (argv : List String) (w : World) (h : parseArgs argv = .help) :
    trace argv w = [.out helpText] ∧ exitCode argv w = 0 := sorry

/-- **R3**: a usage error makes no network request, and exits 2. -/
theorem usage_behavior (argv : List String) (w : World) (m : String)
    (h : parseArgs argv = .usage m) :
    (∀ e ∈ trace argv w, e.isNetwork = false) ∧ exitCode argv w = 2 := sorry

/-- **R4**: the only GET is the fetch request. -/
theorem only_fetch_get (argv : List String) (w : World) (cfg : Cfg)
    (h : parseArgs argv = .ok cfg) :
    ∀ q, Event.get q ∈ trace argv w → q = fetchReq cfg := sorry

/-- **R15**: if the fetch did not yield a valid response: no report, no alert, exit 1. -/
theorem bad_fetch_behavior (argv : List String) (w : World) (cfg : Cfg)
    (h : parseArgs argv = .ok cfg) (hf : ¬ ∃ S R, Fetched cfg w S R) :
    (∀ e ∈ trace argv w, e.isOut = false ∧ e.isPost = false) ∧ exitCode argv w = 1 := sorry

/-- **R30/R40**: on a good fetch, the report is written, and it is the only stdout. -/
theorem report_written (argv : List String) (w : World) (cfg : Cfg) (S : Site) (R : Reading)
    (h : parseArgs argv = .ok cfg) (hf : Fetched cfg w S R) :
    ∀ s, (Event.out s ∈ trace argv w ↔ s = reportFor cfg w S R) := sorry

/-- **R50**: an alert is attempted *if and only if* the alert condition holds. -/
theorem alert_iff (argv : List String) (w : World) (cfg : Cfg)
    (h : parseArgs argv = .ok cfg) :
    (∃ q, Event.post q ∈ trace argv w) ↔ ∃ S R, Fetched cfg w S R ∧ ShouldAlert cfg R := sorry

/-- **R51**: the alert sent is exactly the specified one. -/
theorem alert_content (argv : List String) (w : World) (cfg : Cfg) (q : Request)
    (h : parseArgs argv = .ok cfg) (hq : Event.post q ∈ trace argv w) :
    ∃ S R, Fetched cfg w S R ∧ q = alertReq cfg S R := sorry

/-- **R52**: the report is written before the alert is attempted. -/
theorem report_before_alert (argv : List String) (w : World)
    (pre post : List Event) (q : Request)
    (h : trace argv w = pre ++ Event.post q :: post) :
    ∃ s, Event.out s ∈ pre := sorry

/-- **R60**: every stderr write is a one-line `Error:` message (plus usage text
for usage errors) or the alert notice. -/
theorem stderr_shape (argv : List String) (w : World) (s : String)
    (h : Event.err s ∈ trace argv w) :
    (∃ m, '\n' ∉ m.toList ∧ (s = errLine m ∨ s = errLine m ++ usageText)) ∨
    (∃ cfg, s = alertNotice cfg) := sorry

/-- **R61**: exit statuses. -/
theorem exit_codes (argv : List String) (w : World) :
    exitCode argv w ≤ 2 ∧ (exitCode argv w = 2 ↔ ∃ m, parseArgs argv = .usage m) := sorry

/-- **R62: "it should never silently fail to alert."** If the run exits 0 and
the alert condition held, the alert was delivered. -/
theorem never_silently_fails (argv : List String) (w : World) (cfg : Cfg) (S : Site) (R : Reading)
    (h : parseArgs argv = .ok cfg) (hf : Fetched cfg w S R) (ha : ShouldAlert cfg R)
    (h0 : exitCode argv w = 0) :
    Delivered w (alertReq cfg S R) := sorry

/-- The converse direction: the tool does not fail *spuriously*. A good fetch
with no alert needed, or with the alert delivered, exits 0. -/
theorem succeeds_when_it_should (argv : List String) (w : World) (cfg : Cfg) (S : Site) (R : Reading)
    (h : parseArgs argv = .ok cfg) (hf : Fetched cfg w S R)
    (hd : ShouldAlert cfg R → Delivered w (alertReq cfg S R)) :
    exitCode argv w = 0 := sorry

end LakeLevel
