/-!
# Shared data types

These are part of the *specification*: they fix what kinds of values the
program manipulates (docs/02-formal-model.md §2.1–2.5). Nothing here computes.
-/

namespace LakeLevel

/-- An exact decimal `m / 10^e`. Deliberately the same shape as Lean's
`JsonNumber`, so JSON numbers convert without rounding (A3, R16). -/
structure Dec where
  m : Int
  e : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Seconds since 1970-01-01T00:00:00Z. -/
abbrev Instant := Int

/-- A civil (calendar + wall-clock) time. Not necessarily valid; see `Civil.Valid`. -/
structure Civil where
  y : Nat
  mo : Nat
  d : Nat
  h : Nat
  mi : Nat
  s : Nat
  deriving Repr, DecidableEq, Inhabited

/-- One validated record from the API. `iso` is the timestamp text it came from. -/
structure Reading where
  t : Instant
  level : Dec
  iso : String
  deriving Repr, DecidableEq, Inhabited

/-- Site-level facts from the response. -/
structure Site where
  number : Nat
  name : String
  full : Option Dec
  deriving Repr, DecidableEq, Inhabited

/-- A UTC offset (seconds east of UTC) and abbreviation, supplied by the OS. -/
structure Zone where
  offset : Int
  abbr : String
  deriving Repr, DecidableEq, Inhabited

/-- A threshold as typed on the command line, and its exact value. -/
structure Threshold where
  text : String
  value : Dec
  deriving Repr, DecidableEq

/-- A validated configuration. -/
structure Cfg where
  site : String
  type : String
  json : Bool
  threshold : Option Threshold
  topic : String
  deriving Repr, DecidableEq

inductive ArgResult where
  | help
  | usage (msg : String)
  | ok (cfg : Cfg)
  deriving Repr, DecidableEq

/-- An HTTP request, as a plain value. The shell transmits it; the core only builds it. -/
structure Request where
  method : String
  url : String
  headers : List (String × String)
  body : String
  deriving Repr, DecidableEq

/-- What the world answers to a GET. -/
inductive GetResult where
  | response (status : Nat) (body : String)
  | failed (msg : String)
  deriving Repr, DecidableEq

/-- What the world answers to a POST. -/
inductive PostResult where
  | response (status : Nat)
  | failed (msg : String)
  deriving Repr, DecidableEq

end LakeLevel
