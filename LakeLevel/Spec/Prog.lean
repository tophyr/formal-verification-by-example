import LakeLevel.Types

/-!
# Spec: the program as data, and its meaning in a world

docs/02-formal-model.md §2.0 (3) and §2.7.

`Prog` is a *description* of an interaction. The real shell (`Main.lean`)
interprets it against the actual OS. `Prog.run` interprets it against an
arbitrary mathematical `World`, so theorems of the form `∀ w, P (run p w)`
hold for every possible behavior of the network, clock and time zone.
-/

namespace LakeLevel

inductive Prog where
  | done (exit : Nat)
  | get (req : Request) (k : GetResult → Prog)
  | zoneAt (t : Instant) (k : Zone → Prog)
  | clock (k : Instant → Prog)
  | out (s : String) (k : Prog)
  | err (s : String) (k : Prog)
  | post (req : Request) (k : PostResult → Prog)

/-- Every possible environment. Each kind of question is asked at most once
per run, so a function per question loses no generality. -/
structure World where
  get : Request → GetResult
  zone : Instant → Zone
  now : Instant
  post : Request → PostResult

/-- What an observer of the process would see happen, in order. -/
inductive Event where
  | get (req : Request)
  | zone (t : Instant)
  | clock
  | out (s : String)
  | err (s : String)
  | post (req : Request)
  deriving Repr, DecidableEq

/-- The meaning of a `Prog` in world `w`: the trace of events and the exit status. -/
def Prog.run (p : Prog) (w : World) : List Event × Nat :=
  match p with
  | .done e => ([], e)
  | .get r k => let x := (k (w.get r)).run w; (.get r :: x.1, x.2)
  | .zoneAt t k => let x := (k (w.zone t)).run w; (.zone t :: x.1, x.2)
  | .clock k => let x := (k w.now).run w; (.clock :: x.1, x.2)
  | .out s k => let x := k.run w; (.out s :: x.1, x.2)
  | .err s k => let x := k.run w; (.err s :: x.1, x.2)
  | .post r k => let x := (k (w.post r)).run w; (.post r :: x.1, x.2)

def Event.isNetwork : Event → Bool
  | .get _ | .post _ => true
  | _ => false

def Event.isPost : Event → Bool
  | .post _ => true
  | _ => false

def Event.isOut : Event → Bool
  | .out _ => true
  | _ => false

/-- HTTP success. -/
def ok2xx (status : Nat) : Prop := 200 ≤ status ∧ status < 300

instance (s : Nat) : Decidable (ok2xx s) := by unfold ok2xx; infer_instance

/-- The world delivered this POST. -/
def Delivered (w : World) (q : Request) : Prop :=
  ∃ status, w.post q = .response status ∧ ok2xx status

end LakeLevel
