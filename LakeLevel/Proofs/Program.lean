import LakeLevel.Impl.Program
import LakeLevel.Proofs.Decimal
import LakeLevel.Proofs.Render

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

/-! ## Lemmas: the shape of a run -/

/-- The world's answer to the fetch is fixed, so at most one `(S, R)` is fetched. -/
theorem Fetched.unique {cfg : Cfg} {w : World} {S S' : Site} {R R' : Reading}
    (h : Fetched cfg w S R) (h' : Fetched cfg w S' R') : S = S' ∧ R = R' := by
  obtain ⟨st, body, hg, -, hd⟩ := h
  obtain ⟨st', body', hg', -, hd'⟩ := h'
  rw [hg] at hg'; cases hg'
  rw [hd] at hd'; cases hd'; exact ⟨rfl, rfl⟩

/-- Events that may precede the report: the zone and clock queries (human mode only). -/
def preReport (cfg : Cfg) (R : Reading) : List Event :=
  if cfg.json then [] else [.zone R.t, .clock]

/-- **Every run with a valid configuration has one of two shapes**: (a) nothing
valid was fetched, and the run is the GET then one error line, exit 1; or
(b) the GET, the zone/clock queries, the report, then whatever `finish` does. -/
theorem run_ok_cases (argv : List String) (w : World) (cfg : Cfg) (h : parseArgs argv = .ok cfg) :
    ((¬ ∃ S R, Fetched cfg w S R) ∧
      ∃ m, (main argv).run w = ([.get (fetchReq cfg), .err (errLine (sanitize m))], 1)) ∨
    (∃ S R, Fetched cfg w S R ∧
      (main argv).run w =
        (.get (fetchReq cfg) :: preReport cfg R ++ .out (reportFor cfg w S R) ::
            ((finish cfg S R).run w).1,
         ((finish cfg S R).run w).2)) := by
  unfold main; rw [h]
  cases hg : w.get (fetchReq cfg) with
  | failed m =>
    left; refine ⟨?_, m, by simp [Prog.run, hg]⟩
    rintro ⟨S, R, st, body, hg', -⟩; rw [hg] at hg'; cases hg'
  | response st body =>
    by_cases hs : ok2xx st
    · cases hd : decodeBody (siteNum cfg.site) body with
      | error m =>
        left; refine ⟨?_, m, by simp [Prog.run, hg, hs, hd]⟩
        rintro ⟨S, R, st', body', hg', -, hd'⟩; rw [hg] at hg'; cases hg'; rw [hd] at hd'; cases hd'
      | ok SR =>
        obtain ⟨S, R⟩ := SR
        right; refine ⟨S, R, ⟨st, body, hg, hs, hd⟩, ?_⟩
        by_cases hj : cfg.json
        · simp [Prog.run, hg, hs, hd, hj, preReport, reportFor]
        · simp [Prog.run, hg, hs, hd, hj, preReport, reportFor]
    · left; refine ⟨?_, _, by simp [Prog.run, hg, hs]; rfl⟩
      rintro ⟨S, R, st', body', hg', hs', -⟩; rw [hg] at hg'; cases hg'; exact hs hs'

/-! ## Lemmas: what `finish` (the alert step) can do -/

section finish
variable (cfg : Cfg) (S : Site) (R : Reading) (w : World)

/-- `finish` only POSTs the alert and writes to stderr. -/
theorem finish_events : ∀ e ∈ ((finish cfg S R).run w).1,
    e = .post (alertReq cfg S R) ∨ e = .err (alertNotice cfg) ∨
    ∃ m, e = .err (errLine (sanitize m)) := by
  unfold finish
  cases cfg.threshold with
  | none => simp [Prog.run]
  | some th =>
    by_cases hl : Dec.le th.value R.level = true
    · cases hp : w.post (alertReq cfg S R) with
      | response st =>
        by_cases hs : ok2xx st
        · simp [Prog.run, hl, hp, hs]
        · simp only [Prog.run, hl, hp, hs, ite_true, ite_false]
          intro e he; simp at he; rcases he with rfl | rfl
          · exact .inl rfl
          · exact .inr (.inr ⟨_, rfl⟩)
      | failed m =>
        simp only [Prog.run, hl, hp, ite_true]
        intro e he; simp at he; rcases he with rfl | rfl
        · exact .inl rfl
        · exact .inr (.inr ⟨_, rfl⟩)
    · simp [Prog.run, hl]

theorem finish_exit_le : ((finish cfg S R).run w).2 ≤ 1 := by
  unfold finish
  cases cfg.threshold with
  | none => simp [Prog.run]
  | some th =>
    by_cases hl : Dec.le th.value R.level = true
    · cases hp : w.post (alertReq cfg S R) with
      | response st => by_cases hs : ok2xx st <;> simp [Prog.run, hl, hp, hs]
      | failed m => simp [Prog.run, hl, hp]
    · simp [Prog.run, hl]

theorem finish_post_iff : (∃ q, Event.post q ∈ ((finish cfg S R).run w).1) ↔
    ∃ th, cfg.threshold = some th ∧ Dec.le th.value R.level = true := by
  unfold finish
  cases ht : cfg.threshold with
  | none => simp [Prog.run]
  | some th =>
    by_cases hl : Dec.le th.value R.level = true
    · refine ⟨fun _ => ⟨th, rfl, hl⟩, fun _ => ⟨alertReq cfg S R, ?_⟩⟩
      simp [hl, Prog.run]
    · simp [Prog.run, hl]

theorem finish_exit0 (th : Threshold) (hth : cfg.threshold = some th)
    (hle : Dec.le th.value R.level = true) (h0 : ((finish cfg S R).run w).2 = 0) :
    Delivered w (alertReq cfg S R) := by
  simp only [finish, hth, hle, ite_true] at h0
  cases hp : w.post (alertReq cfg S R) with
  | response st =>
    simp only [Prog.run, hp] at h0
    by_cases hs : ok2xx st
    · exact ⟨st, hp, hs⟩
    · simp [Prog.run, hs] at h0
  | failed m => simp [Prog.run, hp] at h0

theorem finish_exit_ok
    (hd : ∀ th, cfg.threshold = some th → Dec.le th.value R.level = true →
      Delivered w (alertReq cfg S R)) :
    ((finish cfg S R).run w).2 = 0 := by
  unfold finish
  cases ht : cfg.threshold with
  | none => simp [Prog.run]
  | some th =>
    by_cases hl : Dec.le th.value R.level = true
    · obtain ⟨st, hp, hs⟩ := hd th ht hl
      simp [Prog.run, hl, hp, hs]
    · simp [Prog.run, hl]

end finish

/-- Turn a trace-membership into the facts about which part it came from. -/
theorem mem_shape {cfg : Cfg} {S : Site} {R : Reading} {w : World} {e : Event}
    (he : e ∈ Event.get (fetchReq cfg) :: preReport cfg R ++ .out (reportFor cfg w S R) ::
      ((finish cfg S R).run w).1) :
    e = .get (fetchReq cfg) ∨ e = .zone R.t ∨ e = .clock ∨ e = .out (reportFor cfg w S R) ∨
    e ∈ ((finish cfg S R).run w).1 := by
  unfold preReport at he
  by_cases hj : cfg.json
  · simp only [hj, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons] at he
    rcases he with h | h | h
    · exact .inl h
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr h)))
  · simp only [hj, Bool.false_eq_true, ite_false, List.cons_append,
      List.nil_append, List.mem_cons] at he
    rcases he with h | h | h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr h)))

/-! ## The obligations -/

/-- `--help` prints help and exits 0, touching nothing else. -/
theorem help_behavior (argv : List String) (w : World) (h : parseArgs argv = .help) :
    trace argv w = [.out helpText] ∧ exitCode argv w = 0 := by
  simp [trace, exitCode, main, h, Prog.run]

/-- **R3**: a usage error makes no network request, and exits 2. -/
theorem usage_behavior (argv : List String) (w : World) (m : String)
    (h : parseArgs argv = .usage m) :
    (∀ e ∈ trace argv w, e.isNetwork = false) ∧ exitCode argv w = 2 := by
  simp [trace, exitCode, main, h, Prog.run, Event.isNetwork]

/-- **R4**: the only GET is the fetch request. -/
theorem only_fetch_get (argv : List String) (w : World) (cfg : Cfg)
    (h : parseArgs argv = .ok cfg) :
    ∀ q, Event.get q ∈ trace argv w → q = fetchReq cfg := by
  intro q hq; unfold trace at hq
  rcases run_ok_cases argv w cfg h with ⟨-, m, hr⟩ | ⟨S, R, -, hr⟩ <;> rw [hr] at hq
  · simp at hq; exact hq
  · rcases mem_shape hq with h1 | h1 | h1 | h1 | h1
    · cases h1; rfl
    · cases h1
    · cases h1
    · cases h1
    · rcases finish_events cfg S R w _ h1 with h2 | h2 | ⟨_, h2⟩ <;> cases h2

/-- **R15**: if the fetch did not yield a valid response: no report, no alert, exit 1. -/
theorem bad_fetch_behavior (argv : List String) (w : World) (cfg : Cfg)
    (h : parseArgs argv = .ok cfg) (hf : ¬ ∃ S R, Fetched cfg w S R) :
    (∀ e ∈ trace argv w, e.isOut = false ∧ e.isPost = false) ∧ exitCode argv w = 1 := by
  unfold trace exitCode
  rcases run_ok_cases argv w cfg h with ⟨-, m, hr⟩ | ⟨S, R, hF, -⟩
  · rw [hr]; simp [Event.isOut, Event.isPost]
  · exact absurd ⟨S, R, hF⟩ hf

/-- **R30/R40**: on a good fetch, the report is written, and it is the only stdout. -/
theorem report_written (argv : List String) (w : World) (cfg : Cfg) (S : Site) (R : Reading)
    (h : parseArgs argv = .ok cfg) (hf : Fetched cfg w S R) :
    ∀ s, (Event.out s ∈ trace argv w ↔ s = reportFor cfg w S R) := by
  intro s; unfold trace
  rcases run_ok_cases argv w cfg h with ⟨hn, -⟩ | ⟨S', R', hF, hr⟩
  · exact absurd ⟨S, R, hf⟩ hn
  · obtain ⟨rfl, rfl⟩ := Fetched.unique hF hf
    rw [hr]; constructor
    · intro hs
      rcases mem_shape hs with h1 | h1 | h1 | h1 | h1
      · cases h1
      · cases h1
      · cases h1
      · cases h1; rfl
      · rcases finish_events cfg S' R' w _ h1 with h2 | h2 | ⟨_, h2⟩ <;> cases h2
    · rintro rfl; unfold preReport; split <;> simp

/-- **R50**: an alert is attempted *if and only if* the alert condition holds. -/
theorem alert_iff (argv : List String) (w : World) (cfg : Cfg)
    (h : parseArgs argv = .ok cfg) :
    (∃ q, Event.post q ∈ trace argv w) ↔ ∃ S R, Fetched cfg w S R ∧ ShouldAlert cfg R := by
  unfold trace
  rcases run_ok_cases argv w cfg h with ⟨hn, m, hr⟩ | ⟨S, R, hF, hr⟩
  · rw [hr]; constructor
    · rintro ⟨q, hq⟩; simp at hq
    · rintro ⟨S, R, hF, -⟩; exact absurd ⟨S, R, hF⟩ hn
  · rw [hr]; constructor
    · rintro ⟨q, hq⟩
      have hq' : Event.post q ∈ ((finish cfg S R).run w).1 := by
        rcases mem_shape hq with h1 | h1 | h1 | h1 | h1 <;> first | cases h1 | exact h1
      obtain ⟨th, hth, hle⟩ := (finish_post_iff cfg S R w).1 ⟨q, hq'⟩
      exact ⟨S, R, hF, th, hth, (Dec.le_iff _ _).1 hle⟩
    · rintro ⟨S', R', hF', th, hth, hle⟩
      obtain ⟨rfl, rfl⟩ := Fetched.unique hF hF'
      obtain ⟨q, hq⟩ := (finish_post_iff cfg S R w).2 ⟨th, hth, (Dec.le_iff _ _).2 hle⟩
      exact ⟨q, by simp [hq]⟩

/-- **R51**: the alert sent is exactly the specified one. -/
theorem alert_content (argv : List String) (w : World) (cfg : Cfg) (q : Request)
    (h : parseArgs argv = .ok cfg) (hq : Event.post q ∈ trace argv w) :
    ∃ S R, Fetched cfg w S R ∧ q = alertReq cfg S R := by
  unfold trace at hq
  rcases run_ok_cases argv w cfg h with ⟨-, m, hr⟩ | ⟨S, R, hF, hr⟩ <;> rw [hr] at hq
  · simp at hq
  · refine ⟨S, R, hF, ?_⟩
    rcases mem_shape hq with h1 | h1 | h1 | h1 | h1
    · cases h1
    · cases h1
    · cases h1
    · cases h1
    · rcases finish_events cfg S R w _ h1 with h2 | h2 | ⟨_, h2⟩ <;> cases h2; rfl

/-- No `post` occurs before the first `out`. -/
def NoPostBeforeOut : List Event → Prop
  | [] => True
  | .out _ :: _ => True
  | .post _ :: _ => False
  | _ :: rest => NoPostBeforeOut rest

theorem NoPostBeforeOut.spec : ∀ (pre : List Event) (q : Request) (rest : List Event),
    NoPostBeforeOut (pre ++ .post q :: rest) → ∃ s, Event.out s ∈ pre
  | [], _, _, h => by simp [NoPostBeforeOut] at h
  | e :: pre, q, rest, h => by
    cases e with
    | out s => exact ⟨s, by simp⟩
    | post _ => simp [NoPostBeforeOut] at h
    | get _ | zone _ | clock | err _ =>
      obtain ⟨s, hs⟩ := NoPostBeforeOut.spec pre q rest h
      exact ⟨s, by simp [hs]⟩

/-- **R52**: the report is written before the alert is attempted. -/
theorem report_before_alert (argv : List String) (w : World)
    (pre post : List Event) (q : Request)
    (h : trace argv w = pre ++ Event.post q :: post) :
    ∃ s, Event.out s ∈ pre := by
  apply NoPostBeforeOut.spec pre q post
  rw [← h]; unfold trace
  cases hp : parseArgs argv with
  | help => simp [main, hp, Prog.run, NoPostBeforeOut]
  | usage m => simp [main, hp, Prog.run, NoPostBeforeOut]
  | ok cfg =>
    rcases run_ok_cases argv w cfg hp with ⟨-, m, hr⟩ | ⟨S, R, -, hr⟩ <;> rw [hr]
    · simp [NoPostBeforeOut]
    · unfold preReport; split <;> simp [NoPostBeforeOut]

/-- **R60**: every stderr write is a one-line `Error:` message (plus usage text
for usage errors) or the alert notice. -/
theorem stderr_shape (argv : List String) (w : World) (s : String)
    (h : Event.err s ∈ trace argv w) :
    (∃ m, '\n' ∉ m.toList ∧ (s = errLine m ∨ s = errLine m ++ usageText)) ∨
    (∃ cfg, s = alertNotice cfg) := by
  unfold trace at h
  cases hp : parseArgs argv with
  | help => simp [main, hp, Prog.run] at h
  | usage m =>
    simp [main, hp, Prog.run] at h
    exact .inl ⟨sanitize m, sanitize_no_newline m, .inr h⟩
  | ok cfg =>
    rcases run_ok_cases argv w cfg hp with ⟨-, m, hr⟩ | ⟨S, R, -, hr⟩ <;> rw [hr] at h
    · simp at h; exact .inl ⟨sanitize m, sanitize_no_newline m, .inl h⟩
    · rcases mem_shape h with h1 | h1 | h1 | h1 | h1
      · cases h1
      · cases h1
      · cases h1
      · cases h1
      · rcases finish_events cfg S R w _ h1 with h2 | h2 | ⟨m, h2⟩
        · cases h2
        · cases h2; exact .inr ⟨cfg, rfl⟩
        · cases h2; exact .inl ⟨sanitize m, sanitize_no_newline m, .inl rfl⟩

/-- **R61**: exit statuses. -/
theorem exit_codes (argv : List String) (w : World) :
    exitCode argv w ≤ 2 ∧ (exitCode argv w = 2 ↔ ∃ m, parseArgs argv = .usage m) := by
  unfold exitCode
  cases hp : parseArgs argv with
  | help => simp [main, hp, Prog.run]
  | usage m => simp [main, hp, Prog.run]
  | ok cfg =>
    rcases run_ok_cases argv w cfg hp with ⟨-, m, hr⟩ | ⟨S, R, -, hr⟩ <;> rw [hr]
    · simp
    · have := finish_exit_le cfg S R w
      simp only [reduceCtorEq, exists_false, iff_false]; omega

/-- **R62: "it should never silently fail to alert."** If the run exits 0 and
the alert condition held, the alert was delivered. -/
theorem never_silently_fails (argv : List String) (w : World) (cfg : Cfg) (S : Site) (R : Reading)
    (h : parseArgs argv = .ok cfg) (hf : Fetched cfg w S R) (ha : ShouldAlert cfg R)
    (h0 : exitCode argv w = 0) :
    Delivered w (alertReq cfg S R) := by
  unfold exitCode at h0
  rcases run_ok_cases argv w cfg h with ⟨hn, -⟩ | ⟨S', R', hF, hr⟩
  · exact absurd ⟨S, R, hf⟩ hn
  · obtain ⟨rfl, rfl⟩ := Fetched.unique hF hf
    rw [hr] at h0
    obtain ⟨th, hth, hle⟩ := ha
    exact finish_exit0 cfg S' R' w th hth ((Dec.le_iff _ _).2 hle) h0

/-- The converse direction: the tool does not fail *spuriously*. A good fetch
with no alert needed, or with the alert delivered, exits 0. -/
theorem succeeds_when_it_should (argv : List String) (w : World) (cfg : Cfg) (S : Site) (R : Reading)
    (h : parseArgs argv = .ok cfg) (hf : Fetched cfg w S R)
    (hd : ShouldAlert cfg R → Delivered w (alertReq cfg S R)) :
    exitCode argv w = 0 := by
  unfold exitCode
  rcases run_ok_cases argv w cfg h with ⟨hn, -⟩ | ⟨S', R', hF, hr⟩
  · exact absurd ⟨S, R, hf⟩ hn
  · obtain ⟨rfl, rfl⟩ := Fetched.unique hF hf
    rw [hr]
    exact finish_exit_ok cfg S' R' w fun th hth hle => hd ⟨th, hth, (Dec.le_iff _ _).1 hle⟩

end LakeLevel
