import LakeLevel
import Std.Time

/-!
# The imperative shell

Everything in this file is **trusted, not proved** (docs/06). Its only job is
to interpret each `Prog` constructor with the matching real-world primitive.
All decisions (what to fetch, what to print, whether to alert, which exit
status) were made by the verified `LakeLevel.main`, which this file only
runs. Keep it short enough to audit by eye.
-/

open LakeLevel

/-- Run curl. Any failure to even start it becomes a `.failed` answer. -/
def curl (args : Array String) (stdin : String := "") : IO (Except String String) := do
  try
    let child ← IO.Process.spawn
      { cmd := "curl", args, stdin := .piped, stdout := .piped, stderr := .piped }
    let (stdinH, child) ← child.takeStdin
    stdinH.putStr stdin
    stdinH.flush
    let _ := stdinH  -- dropped here, closing curl's stdin
    let out ← child.stdout.readToEnd
    let err ← child.stderr.readToEnd
    let code ← child.wait
    if code == 0 then return .ok out else return .error s!"curl: {err.trimAscii}"
  catch e => return .error s!"could not run curl: {e}"

/-- Common curl flags: quiet but report errors, 30 s total (A21), HTTPS only,
and print the status code on a final line of its own. -/
def curlBase (req : Request) : Array String :=
  #["--silent", "--show-error", "--max-time", "30", "--proto", "=https",
    "--request", req.method, "--write-out", "\n%{http_code}"] ++
  (req.headers.toArray.flatMap fun (k, v) => #["--header", s!"{k}: {v}"])

/-- Split curl's output into body and the status line it appended. -/
def splitStatus (out : String) : Option (String × Nat) :=
  match out.splitOn "\n" |>.reverse with
  | code :: rest => code.toNat?.map fun n => ("\n".intercalate rest.reverse, n)
  | [] => none

def httpGet (req : Request) : IO GetResult := do
  match ← curl (curlBase req ++ #["--", req.url]) with
  | .error m => return .failed m
  | .ok out => match splitStatus out with
    | some (body, st) => return .response st body
    | none => return .failed "curl produced no status code"

def httpPost (req : Request) : IO PostResult := do
  match ← curl (curlBase req ++ #["--data-binary", "@-", "--output", "/dev/null", "--", req.url])
      req.body with
  | .error m => return .failed m
  | .ok out => match splitStatus out with
    | some (_, st) => return .response st
    | none => return .failed "curl produced no status code"

/-- The OS's zone at instant `t` (honors `TZ`). If the tz database can't
answer, fall back to UTC. This affects only how the time is displayed. -/
def zoneAt (t : Instant) : IO Zone := do
  try
    let rules ← Std.Time.Database.defaultGetLocalZoneRules
    let z := rules.timezoneAt (Std.Time.Timestamp.ofSecondsSinceUnixEpoch (.ofInt t))
    return ⟨z.offset.second.val, z.abbreviation⟩
  catch _ => return ⟨0, "UTC"⟩

def now : IO Instant := return (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val

/-- The interpreter: one line per `Prog` constructor. -/
partial def interp : Prog → IO UInt32
  | .done e => return e.toUInt32
  | .get r k => do interp (k (← httpGet r))
  | .zoneAt t k => do interp (k (← zoneAt t))
  | .clock k => do interp (k (← now))
  | .out s k => do IO.print s; (← IO.getStdout).flush; interp k
  | .err s k => do IO.eprint s; (← IO.getStderr).flush; interp k
  | .post r k => do interp (k (← httpPost r))

def main (args : List String) : IO UInt32 := interp (LakeLevel.main args)
