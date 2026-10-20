# Stage 2: The formal model

> **Input:** [`01-requirements.md`](01-requirements.md) (atomic requirements,
> each tagged P/T/I/A).
> **Output:** mathematical objects and functions precise enough that a
> proof assistant could check them, written in ordinary math notation first
> so the ideas are visible before Lean's syntax gets in the way.

## 2.0 Three ideas this stage introduces

**(1) A spec must not be a copy of the code.** For each piece of behavior we
write a *specification* that says what a correct answer looks like without
saying how to compute it. Later, an *implementation* computes an answer, and
a *proof* connects the two. If the spec computes the answer the same way the
implementation does, the proof is a tautology: a mistake in one is the same
mistake in the other, and the proof goes through anyway.

> This is the formal-methods version of a test whose expected value was
> computed by calling the function under test. A spec that is a copy of the
> algorithm will "verify" a buggy algorithm just as happily.

So every spec below is written in a *different style* from its eventual
implementation:

| Style | Example here | The implementation will instead |
|---|---|---|
| **Relational** (says when an answer is acceptable) | rounding: "*k* is within ½ of *x*, ties away from zero" (§2.1) | use integer division |
| **Characterization** (rules that only one function satisfies) | calendar: "day(1970-01-01) = 0, day(next date) = day + 1" (§2.2) | use a closed-form formula with divisions by 4, 100, 400, 153 and 146097 |
| **Inverse** (round trip) | timestamps: `parseTs(s) = some t` exactly when `s = iso(c)` for a valid civil time `c` with `secs(c) = t` (§2.2) | pattern-match the 20 characters |
| **Declarative over indices** | "the first element with the maximal instant" (§2.4) | be a loop that keeps the best reading so far |
| **Whole-run properties** (∀ worlds) | "never exit 0 having failed to alert" (§2.7) | be the whole tool; idea (3) is what makes these statable |
| **Template equation** (the fallback) | the exact text of the human report (§2.6) | be that template; validated against PRD examples instead of proved meaningful |

> **Nothing checks this.** A spec that repeats the implementation's
> algorithm type-checks, can be proved, and passes every check that later
> stages add, including the planted-bug checks: change the implementation
> and a proof against a copied spec breaks just as it would against an
> independent one. Formal verification as a method doesn't prevent a
> tautological spec. Each spec's independence is a decision made by the
> person writing it and checked by the person reviewing it.

Three habits keep the specs here independent:

- **The spec comes first.** Stage 3 writes the whole spec before Stage 4
  writes any implementation, so there is no code to copy.
- **Describe how to recognize a correct answer**, not how to produce one.
  Checking an answer is usually simpler than computing it: "within ½ of
  *x*, ties away from zero" is easier to state than the integer division
  that achieves it.
- **Check some specs against answers from outside.** Where a spec allows
  exactly one answer (the uniqueness lemmas for `RoundsTo` and `Latest`),
  tests whose expected values come from outside the code (the PRD's
  examples, GNU `date`) also confirm the spec on those examples. Away from
  the examples, a spec and an implementation that make the same mistake
  still agree.

When no independent description can be found, the spec is the code: the
Template row above, checked by tests with expected values from elsewhere.

**(2) Functional core, imperative shell.** Proofs are about mathematical
functions. Network, clocks and time zones aren't functions. So the tool is
split into a **pure core**, which never performs I/O (everything it needs
comes in as arguments and everything it produces goes out as return values),
and a **shell**, which performs the I/O and calls the core. Lean enforces the
split: a function that performs I/O returns an `IO` value, and a function
whose type doesn't mention `IO` can't perform I/O (apart from debug tracing
and deliberately unsafe escape hatches).

The most direct way to apply the pattern would be a shell that calls pure
functions for every computation:

```
main(argv):
  cfg      = parseArgs(argv)                  # pure
  response = httpGet(fetchRequest(cfg))       # I/O
  reading  = decode(response)                 # pure
  print(report(reading))                      # I/O
  if shouldAlert(cfg, reading):               # pure
    status = httpPost(alertRequest(cfg, reading))   # I/O
    if status is not 2xx:
      exit 1
  exit 0
```

Every function the shell calls can be proved, but the shell itself still
decides what happens: what to fetch first, that the report is printed before
the alert is sent (R52), and that a failed alert means exit 1 (R62). Those
decisions are lines of shell code, and no theorem covers them. The tool would
be mostly unproven code with small proven pieces in it.

**(3) The computation as a value.** This design reverses that relationship.
The core makes every decision, including R52 and R62, and the shell only
carries out the core's requests. The tool becomes mostly proven code, with a
few trusted components inside it (such as the JSON parser, §2.8) and a thin
unproven layer around it.

The core can't perform I/O, so it can't make a request and then decide what
to do with the answer. Instead it returns a description of the whole
computation, as a value of type `Prog`. (`Prog` always means this value,
never the `lake-level` tool as a whole.) A `Prog` is a chain of steps. Each
step either asks the outside world one question, prints some text, or ends
the run. The chain doesn't exist in advance: when the core returns, only the
first step exists, along with a function that computes the next step once the
answer is known, and every later step works the same way.

The answers come from the **world**: whoever replies to the HTTP request, the
system clock, the time-zone database. The world supplies one operation for
each kind of question. An **executor** works through the chain: it takes the
current step, gets the answer from the world, and calls the step's `next`
function with it to get the following step. Each step is split in two. The
world supplies how to answer the question, and the step supplies what to do
with the answer:

| Step | The step holds | The world supplies | `next` takes |
|---|---|---|---|
| `httpGet` | a request, and `next` | `get : Request → GetResult` | a `GetResult` |
| `clock` | `next` | `now : Instant` | an `Instant` |
| `zoneAt` | an instant, and `next` | `zone : Instant → Zone` | a `Zone` |
| `httpPost` | a request, and `next` | `post : Request → PostResult` | a `PostResult` |
| `out` | some text, and `next` | nothing; the executor prints the text to stdout | nothing; `next` is already a `Prog` |
| `err` | some text, and `next` | nothing; the executor prints the text to stderr | nothing; `next` is already a `Prog` |
| `done` | an exit status | nothing; the executor stops | (nothing comes after) |

(`A → B` is the type of functions from `A` to `B`.) In every row, the type
the world produces is the type `next` takes. No step receives an answer
directly; the answer goes into `next`, which is ordinary pure code in the
core, and `next` decides which step comes after. A function like `next`,
which receives the result of a step and says what to do after it, is a
**continuation**. The types:

- `Request`: an HTTP method, URL, headers and body, as plain data.
- `GetResult`: `response(status, body)`, or `failed(message)` if no response
  came back (curl couldn't connect, or timed out).
- `PostResult`: `response(status)` or `failed(message)`.
- `Instant`: seconds since 1970-01-01T00:00:00Z (§2.2).
- `Zone`: a UTC offset and an abbreviation, such as CDT (§2.2).

The R62 decision from the sketch is now inside the `next` of the `httpPost`
step: given a failed POST, it returns an `err` step that prints an error and
ends with exit 1. Taken together, the four operations make up a world:

```
W = (get : Request → GetResult,  now : Instant,  zone : Instant → Zone,  post : Request → PostResult)
```

When the tool runs for real, the world is the actual network, clock and
time-zone database, and the executor is the shell. But any four functions
with these types make up a world, and a `Prog` can be run against any of
them. (Lean's own `IO` type couldn't be used this way: an `IO` value is
opaque, and can't be inspected or run against a different world.) Running a
`Prog` against a world produces a **trace**, the list of events an observer
would see, and an exit status. Properties of the whole tool then become
statements about functions, quantified over **every world** (§2.7). That's
how R3 ("no network request on a usage error") and R52 ("the report is
written before the alert is attempted"), which Stage 1 could only tag
**I**nspect, become **P**roved.

What's left to inspect is that the executor carries out each kind of step
with the right real operation. It makes no decisions.

---

## 2.1 Numbers

**Exact decimals.** `Dec = ℤ × ℕ`, written ⟨m, e⟩, denoting

```
⟦⟨m, e⟩⟧ = m / 10^e  ∈ ℚ
```

This is exactly the representation Lean's JSON parser produces for a JSON
number (`JsonNumber = {mantissa : Int, exponent : Nat}`; verified:
`677.58 ↦ ⟨67758, 2⟩`, `681.0 ↦ ⟨6810, 1⟩`). Different pairs may denote the
same rational (`⟨6810,1⟩`, `⟨681,0⟩`); all *semantics* go through ⟦·⟧.

**Comparison** (R50, A5). *Spec:* `a ≼ b ⇔ ⟦a⟧ ≤ ⟦b⟧` in ℚ.
*Implementation will be* cross-multiplication on integers. *Obligation:*
`le a b = true ⇔ ⟦a⟧ ≤ ⟦b⟧`.

**Rounding** (A4, R31). For `x ∈ ℚ`, `k ∈ ℤ` is a **correct rounding of x**,
written `RoundsTo(x, k)`, iff

```
|x − k| < ½   ∨   ( |x − k| = ½  ∧  |k| > |x| )
```

*Lemma (uniqueness):* for every x there is exactly one such k.
*Obligation:* `round(n, d)` satisfies `RoundsTo(⟦d⟧ · 10ⁿ, round(n, d))`.

**Decimal syntax** (A6). The language

```
DecLit = "-"? [0-9]+ ( "." [0-9]+ )?
```

with denotation `den("-"? a "." b) = ±(val(a ++ b)) / 10^|b|`, where
`val(digits) = Σ dᵢ·10^(len−1−i)` (positional notation).
*Obligations:* `parseDec(s) = some d ⇒ s ∈ DecLit ∧ ⟦d⟧ = den(s)`, and
`s ∈ DecLit ⇒ parseDec(s) ≠ none`.

**Fixed-point rendering** (R31, R32). `fixed(n, k)` renders `k / 10ⁿ`.
*Obligations:*
- *shape:* `fixed(n, k) ∈ "-"? ("0" | [1-9][0-9]*) "." [0-9]{n}` (for n ≥ 1);
  begins with `-` iff `k < 0`;
- *meaning:* `parseDec(fixed(n, k)) = some d` with `⟦d⟧ = k / 10ⁿ`;
- `signed(n, k) = "+" ++ fixed(n, k)` if `k ≥ 0`, else `fixed(n, k)`.

So "render to 2 dp" of a level `L` is `fixed(2, round(2, L))`, and the
obligations together say: the text, read back, is within 0.005 of the true
level, with ties going away from zero, in the expected shape.

## 2.2 Time

**Civil time.** `Civil = (y, mo, d, h, mi, s) ∈ ℕ⁶`.

```
leap(y)          ⇔ 4 | y ∧ (100 ∤ y ∨ 400 | y)
dim(y, mo)       = 29 if mo = 2 ∧ leap(y);  28 if mo = 2;  30 if mo ∈ {4,6,9,11};  31 otherwise
ValidDate(y,mo,d)⇔ 1 ≤ y ≤ 9999 ∧ 1 ≤ mo ≤ 12 ∧ 1 ≤ d ≤ dim(y, mo)
Valid(c)         ⇔ ValidDate(y,mo,d) ∧ h < 24 ∧ mi < 60 ∧ s < 60
```

**The day number, by characterization** (R23). Define the *successor date*,
the obvious "tomorrow":

```
next(y, mo, d) = (y, mo, d+1)     if d < dim(y, mo)
               = (y, mo+1, 1)     if d = dim(y, mo) ∧ mo < 12
               = (y+1, 1, 1)      if d = dim(y, mo) ∧ mo = 12
```

*Spec:* `days : Date → ℤ` must satisfy

```
days(1970, 1, 1) = 0
days(next(D))    = days(D) + 1        for all valid D
```

Any function satisfying these agrees with every other one on all valid dates
from 0001-01-01 on (by induction along `next`), so this *is* the proleptic
Gregorian day count, specified without a formula. The implementation will
use Howard Hinnant's closed-form `days_from_civil` (divisions by 4, 100, 400,
153, 146097), and Stage 5 proves it satisfies both equations.

**Instants.** `Instant = ℤ` (seconds since 1970-01-01T00:00:00Z).
`secs(c) = 86400·days(y,mo,d) + 3600h + 60mi + s`.

*Obligations:*
- `secs` is injective on valid civil times;
- **inverse:** `civilOf : ℤ → Civil` with `Valid(civilOf(t))` and
  `secs(civilOf(t)) = t` for every t in range. Together with injectivity
  this means `civilOf(t)` is *the* civil time of t, not just *a* plausible
  one.

**Timestamps** (A2, R14, R41). `iso(c) = YYYY "-" MM "-" DD "T" hh ":" mm ":" ss "Z"`
(zero-padded fixed width). *Spec of the parser:*

```
parseTs(s) = some t   ⇔   ∃ c. Valid(c) ∧ 1970 ≤ c.y ∧ s = iso(c) ∧ t = secs(c)
```

This one equation captures strictness (only the canonical form is
accepted), range checking, and the meaning of the result. It implies R41:
`iso(civilOf(t)) = s` whenever `parseTs(s) = some t`.

**Local time** (A11, R34). Given a zone `z = (offset ∈ ℤ, abbr)` supplied by
the world for instant t: `local(t, z) = civilOf(t + offset)`.

**12-hour clock** (R33). `h12 : {0..23} → {1..12} × {AM, PM}`,
`h12(0) = (12, AM)`, `h12(h) = (h, AM)` for 1 ≤ h ≤ 11, `h12(12) = (12, PM)`,
`h12(h) = (h−12, PM)` for 13 ≤ h ≤ 23.
*Obligation:* bijective, and `h12⁻¹(hh, p) = (hh mod 12) + (12 if p = PM)`.
(The domain is finite, so this is provable by exhaustive check.)

**Age** (A12). `age(now, t) = round(0, (now − t)/60)`, reusing `RoundsTo`.

## 2.3 The response

Let `J` be the decoded JSON value. Write `J.k` for the member named k.

```
Rec(r)       ⇔ r.dateTime is a string s with parseTs(s) = some t
               ∧ r.value1 is a JSON number d
             ↦ Reading(t, d, s)

ValidResp(site, J) ⇔ J is an object
                   ∧ J.value1Type = "Head"
                   ∧ (J.siteNumber absent ∨ J.siteNumber = site)
                   ∧ J.records = [r₀ … rₙ₋₁], n ≥ 1, ∀i. Rec(rᵢ)
```

`Site = (number, name, full?)` with `name = J.siteName` if it is a string,
else `"site " ++ decimal(number)`; `full? = J.lakeOperatingRangeMax` if a
number, else `none`.

*Obligation (R10–R15):*

```
decode(site, J) = ok(S, R)  ⇔  ValidResp(site, J) ∧ S is the Site of J ∧ Latest(readings(J), R)
decode(site, J) = error(m)  ⇔  ¬ValidResp(site, J)
```

## 2.4 Selecting the reading (R20–R22)

Declarative spec over list indices, for a list `rs` of readings:

```
Latest(rs, r) ⇔ ∃ i < |rs|.  rs[i] = r
                           ∧ ∀ j < |rs|.  rs[j].t ≤ r.t
                           ∧ ∀ j < i.     rs[j].t < r.t
```

(r is in the list; nothing is later; nothing *before* it is as late, i.e.
it's the first of the maxima.) *Lemma:* Latest is functional (at most one r).
*Obligation:* `select(rs) = some r ⇔ rs ≠ [] ∧ Latest(rs, r)`.

## 2.5 Arguments (R1–R2)

`Cfg = (site : Digits₁..₉, type : [a-z]₁..₃₂, json : 𝔹, threshold : (DecLit × Dec)?, topic : Topic)`.

`parseArgs : List Str → help | usage(msg) | ok(Cfg)`.

*Obligations:*
- *soundness:* `ok(cfg)` ⇒ every field satisfies its syntax (so R6, URL
  safety, follows from the field syntax alone);
- *no duplicates:* an argv mentioning any option twice yields `usage`;
- *defaults:* `parseArgs([]) = ok(3963, lakelevel, false, none, csarbora)`;
- *faithfulness:* if `parseArgs(argv) = ok(cfg)` and argv contains
  `--site v` or `--site=v`, then `cfg.site = v` (and likewise per option).

**URL safety** (R6). `url(cfg) = P ++ cfg.site ++ "/" ++ cfg.type` with
`P = "https://hydromet.lcra.org/api/GetDataBySite/"`; obligation: every
character after `P` is in `[0-9a-z/]`, and exactly one `/` occurs after `P`.
Similarly `"https://ntfy.sh/" ++ topic` has no `/`, `?`, `#` after the
prefix.

## 2.6 Rendering

These are **template equations**: the spec *is* the format, taken from
Stage 1 R30/R51. We prove them only in the weak sense that the
implementation is literally this template applied to the verified pieces
above; their *meaning* rests on the pieces (rounding, calendar, h12) being
right, which is proved. We also check them against the PRD's examples.

```
human(S, R, z, now) =
  S.name ⏎
  "  Most recent lake level: " fixed(2, round(2, R.level)) " ft (MSL)" ⏎
  "  Observed: " clock12(local(R.t, z)) " " z.abbr " (" ageText(age(now, R.t)) ")" ⏎
  [ if S.full = some F:
    "  Full pool: " fixed(1, round(1, F)) " ft  (" signed(2, round(2, F − R.level)) " ft from full)" ⏎ ]

json(S, R) = { site: S.name, siteNumber: S.number, level_ft: R.level,
               unit: "Head", observed_utc: R.iso, operating_range_max_ft: S.full ?? null }

alertReq(cfg, S, R) = POST ("https://ntfy.sh/" ++ cfg.topic)
  headers [Title: "Lake level alert: " L2 " ft", Priority: high, Tags: warning,ocean]
  body    S.name " lake level is " L2 " ft (MSL) as of " R.iso "." ⏎ "Level has reached the alert threshold."
  where L2 = fixed(2, round(2, R.level))
```

Note `F − R.level` is computed exactly on `Dec` before rounding (A13), not
as a difference of rounded values.

## 2.7 The whole program, and properties over all worlds

`main(argv) : Prog` is defined by composing the above. A **world** (§2.0 (3)) is

```
W = (get : Request → GetResult,  zone : Instant → Zone,  now : Instant,  post : Request → PostResult)
```

and `run(p, W) = (trace, exit)` feeds W's answers into p, recording each
effect as an event: `Get(req) | Zone(t) | Clock | Out(s) | Err(s) | Post(req)`.
(Each kind of question is asked at most once per run, so modelling the world
as functions loses no generality: any sequence of environmental answers is
some W.)

*Trace obligations*, each quantified **∀ argv, ∀ W**:

| Req | Property of `run(main(argv), W)` |
|---|---|
| R3 | `parseArgs(argv)` is not `ok` ⇒ trace contains no `Get` and no `Post` |
| R4 | trace contains at most one `Get`, and it is `Get(fetchReq(cfg))` |
| R15 | `decode` fails ⇒ no `Out`, no `Post`, exit = 1 |
| R50 | trace contains `Post(_)` ⇔ cfg has threshold θ ∧ decode = ok(S, R) ∧ ⟦R.level⟧ ≥ ⟦θ⟧ |
| R51 | every `Post(q)` has `q = alertReq(cfg, S, R)` |
| R52 | every `Post` is preceded by an `Out` |
| R60 | every `Err(s)` has `s = "Error: " ++ m ++ "⏎"` with ⏎ ∉ m (+ usage line for usage errors) |
| R61 | exit ∈ {0, 1, 2}; exit = 2 ⇔ usage error |
| **R62** | **threshold given ∧ level ≥ threshold ∧ post returned failure ⇒ exit ≠ 0** |

R62 is the formal statement of the PRD's most important sentence: *it should
never silently fail to alert.*

## 2.8 What the model deliberately does not contain (→ trusted base)

| Assumed (A) | Why it can't be proved here |
|---|---|
| Lean's `Json.parse` maps JSON text to the value it denotes | third-party code; unverified |
| `curl` sends the request we built, honors the 30 s timeout, reports status truthfully | external program |
| The OS tz database gives the right offset/abbreviation | external data |
| The system clock is right | outside the program |
| Lean's compiler produces machine code faithful to the definitions | compiler is unverified (the *kernel* checks proofs; the *compiler* is separate) |
| Lean's kernel is sound, and `propext`, `Quot.sound`, `Classical.choice` are consistent | the foundation everything rests on |

Stage 6 audits this list against the final code.

## 2.9 Traceability: requirement → model element

| Req | Model element | Spec style |
|---|---|---|
| R1–R2 | `parseArgs` soundness / defaults / faithfulness / no-dup | relational |
| R3, R52 | trace properties | ∀-world |
| R4, R6 | `fetchReq`, URL safety | template + char-class |
| R10–R15 | `ValidResp`, `decode` ⇔ | declarative |
| R16 | `Dec` from `JsonNumber` | definitional (A for parser) |
| R20–R22 | `Latest` | declarative over indices |
| R23 | `days` characterization | characterization |
| R30 | `human` | template |
| R31–R32 | `RoundsTo`, `fixed`, `signed`, `parseDec` | relational + inverse |
| R33 | `h12` | finite bijection |
| R34 | `civilOf` inverse | inverse |
| R40–R41 | `json`, `parseTs` ⇔ `iso` | template + inverse |
| R50–R51 | trace properties, `alertReq` | ∀-world + template |
| R60–R62 | trace properties | ∀-world |
