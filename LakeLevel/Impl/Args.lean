import LakeLevel.Spec.Args
import LakeLevel.Impl.Decimal

/-! # Impl: command-line parsing and the fetch request (A20) -/

namespace LakeLevel

/-- Options seen so far; `none` = not given. -/
structure ArgState where
  site : Option String := none
  type : Option String := none
  json : Bool := false
  threshold : Option String := none
  topic : Option String := none
  help : Bool := false

def valuedOpts : List String := ["--site", "--type", "--threshold", "--ntfy-topic"]

/-- Record a valued option; giving one twice is an error. -/
def setOpt (st : ArgState) (o v : String) : Except String ArgState :=
  let twice := throw s!"{o} given more than once"
  if o = "--site" then (if st.site.isSome then twice else pure { st with site := some v })
  else if o = "--type" then (if st.type.isSome then twice else pure { st with type := some v })
  else if o = "--threshold" then
    (if st.threshold.isSome then twice else pure { st with threshold := some v })
  else if o = "--ntfy-topic" then (if st.topic.isSome then twice else pure { st with topic := some v })
  else throw s!"unknown option {o}"

/-- Split `--opt=value` at the first `=`. -/
def splitEq (tok : String) : Option (String × String) :=
  let cs := tok.toList
  match cs.dropWhile (· ≠ '=') with
  | '=' :: v => some (String.ofList (cs.takeWhile (· ≠ '=')), String.ofList v)
  | _ => none

def parseLoop : List String → ArgState → Except String ArgState
  | [], st => pure st
  | tok :: rest, st =>
    if tok = "--help" then parseLoop rest { st with help := true }
    else if tok = "--json" then
      (if st.json then throw "--json given more than once" else parseLoop rest { st with json := true })
    else if tok ∈ valuedOpts then
      match rest with
      | v :: rest' => do parseLoop rest' (← setOpt st tok v)
      | [] => throw s!"{tok} needs a value"
    else match splitEq tok with
      | some (o, v) => if o ∈ valuedOpts then do parseLoop rest (← setOpt st o v)
                       else throw s!"unknown option {o}"
      | none => throw s!"unexpected argument {tok}"

/-- Turn the options seen into a validated configuration. -/
def finalize (st : ArgState) : ArgResult :=
  let site := st.site.getD defaultCfg.site
  let type := st.type.getD defaultCfg.type
  let topic := st.topic.getD defaultCfg.topic
  if ¬ SiteSyntax site then .usage s!"--site must be 1-9 digits: {site}"
  else if ¬ TypeSyntax type then .usage s!"--type must be 1-32 lowercase letters: {type}"
  else if ¬ TopicSyntax topic then .usage s!"--ntfy-topic must match [-_A-Za-z0-9]\{1,64}: {topic}"
  else match st.threshold with
    | none => .ok { site, type, json := st.json, threshold := none, topic }
    | some text => match parseDec text with
      | some d => .ok { site, type, json := st.json, threshold := some ⟨text, d⟩, topic }
      | none => .usage s!"--threshold must be a decimal number like 685 or 680.5: {text}"

def parseArgs (argv : List String) : ArgResult :=
  match parseLoop argv {} with
  | .error m => .usage m
  | .ok st => if st.help then .help else finalize st

/-- The numeric value of a validated site string. -/
def siteNum (s : String) : Nat := digitsVal s.toList

/-- The GET request for a configuration (R4). -/
def fetchReq (cfg : Cfg) : Request :=
  { method := "GET", url := hydrometPrefix ++ cfg.site ++ "/" ++ cfg.type,
    headers := [("User-Agent", "lake-level/1.0")], body := "" }

end LakeLevel
