# Stage 5: Proofs, from "works on examples" to "works on all inputs"

> **Input:** Stage 4's implementation and 48 `sorry`'d obligations.
> **Output:** all 48 proved, checked by Lean's kernel, depending on no
> axioms beyond Lean's standard three.

```
$ lake env lean scripts/Audit.lean
theorems proved from standard axioms only: 139 (obligations + helper lemmas)
obligations (scripts/obligations.txt) fully proved: 48/48
theorems still depending on sorry: 0
definitions still depending on sorry: 0
```

## 5.1 What was proved, in plain English

For **every** command line, **every** HTTP response anyone could send,
**every** clock reading, time zone and ntfy outcome:

- **It never silently fails to alert** (`never_silently_fails`, R62). If
  a threshold was given, the response was valid, the exact level was at or
  above it, and the run exited 0, then ntfy accepted the alert with a 2xx.
- **It alerts if and only if it should** (`alert_iff`, R50), and only after
  the report is printed (`report_before_alert`, R52), with exactly the
  specified content (`alert_content`, R51).
- **Bad input never produces a report or an alert** (`bad_fetch_behavior`,
  R15). A usage error never touches the network (`usage_behavior`, R3).
- **It reports the right reading**: `decode` accepts exactly the responses
  the declarative `ValidResp` describes, and returns the reading the
  declarative `Latest` describes (`decode_ok_iff`, `select_iff`).
- **The arithmetic is right**: comparisons are exact rational comparisons
  (`Dec.le_iff`); rounding meets the relational spec (`Dec.round_spec`),
  whose answer is unique (`RoundsTo.unique`); rendered numbers read back as
  exactly the rounded value (`parseDec_fixed`).
- **The calendar is right**: `days` satisfies the characterization
  (`days_spec`), so it *is* the proleptic Gregorian day count; `civilOf`
  inverts `secs`; the timestamp parser accepts exactly the canonical
  renderings of real dates (`parseTs_spec`).
- **URLs can't be injected into** (`fetchReq_url_safe`, `alertReq_url_safe`).

## 5.2 Techniques used (with where to look)

### Bridge lemmas: do the math in ℚ, the proof in ℤ
Specs are stated over `Rat` because that's what they mean. But Lean's
automation is strong for linear integer arithmetic (`omega`) and weak for
division by variables in ℚ. So one bridge lemma clears denominators
(`a/b ≤ c/d ↔ a·d ≤ c·b` for positive `b, d`), and everything after it works
on integers. → `Proofs/DecimalLemmas.lean`

### Splitting a proof into algebra and an exhaustive check
The calendar's year-of-era recovery, `(doe − doe/1460 + doe/36524 −
doe/146096)/365 = yoe`, was too much for `omega` to prove directly. It was
split into:
1. *monotonicity*, which `omega` proves; and
2. the formula is right at the **400** boundaries of an era, which
   `decide +kernel` checks one by one.

Together these cover all 146,097 days of an era without checking them
individually. Exhaustive checking is legitimate proof when the kernel does
it. (`native_decide`, which would trust the compiler instead, was
forbidden.) → `Proofs/CalendarLemmas.lean`

### Shape lemmas: reason about *all* worlds by naming the few possible shapes
`run_ok_cases` proves every run with a valid configuration has one of two
shapes: *GET + one error line, exit 1* or *GET + report + whatever the alert
step does*. Each whole-program theorem is then a few lines of case analysis
on that lemma. → `Proofs/Program.lean`

### Sanity theorems about the spec itself
`RoundsTo.unique` and `Latest.unique` prove the *spec* admits at most one
answer. A spec that allowed two answers would let two different "verified"
programs disagree. These are the formal analogue of testing your tests.

### Proof-driven refactoring
`decode` was a single `do` block whose control flow was hard to unfold in
proofs. It was split into named steps (`checkHead`, `checkSite`,
`getRecords`, …), each with its own small lemma. Behavior, check order and
messages were unchanged, and the tests still pass. The version that was
easier to prove was also easier to read.

## 5.3 What the proofs found

- **The spec was weaker than it needed to be.** `fixed_shape`, `fixed_neg`
  and `parseDec_fixed` were stated with a hypothesis `1 ≤ n` that the
  proofs never used: Lean flagged it as an unused variable. The
  hypotheses were removed, so the theorems now cover `n = 0` (integer
  rendering, which `ageText` uses), and they're strictly stronger.
- **A tool can fail silently, too.** `omega` (the linear-arithmetic
  decision procedure) ignores hypotheses whose type is written `Instant`,
  which is just an abbreviation for `Int`. It doesn't error; it just
  doesn't use them, and then reports it can't prove the goal. Two
  independent proof efforts hit this. Fix: restate with `(_ : Int)`. It
  could never make a false theorem pass, only make a true one look
  unprovable. Still, it's worth knowing that even the prover's own tools
  can quietly skip information you gave them.

## 5.4 Do the proofs actually constrain the code?

A proof that still goes through with a broken implementation isn't
checking anything. So the same experiment as Stage 4's "testing the tests" was run
against the proofs: plant a bug, build **only the proof library** (tests
excluded), and require that some proof breaks.

| Planted bug | Broke | Stage 4 tests catch it? |
|---|---|---|
| `select` keeps the *last* of tied readings | `Proofs/Select.lean` | yes |
| rounding ties toward zero | `Proofs/DecimalLemmas.lean` | yes |
| midnight shown as `00 AM` | `Proofs/Calendar.lean` | yes |
| exit 0 when ntfy returns an HTTP error | `Proofs/Program.lean` (R62) | yes |
| calendar off by one day | `Proofs/CalendarLemmas.lean` | yes |
| `--site` allowed twice | `Proofs/Args.lean` | yes |
| reject responses that lack `siteNumber` | `Proofs/DecodeLemmas.lean` | **no** |

The last row is the main argument for this stage. Every
fixture happened to contain a `siteNumber`, so the test suite passed with
that bug in place. The proof doesn't care what the fixtures contain. (A
fixture without `siteNumber` was then added, so the tests catch it too.)

Because `lake-level` imports the proof library, **a bug that breaks a proof
also breaks the build of the binary**, so the broken version can't be
built.

## 5.5 Where the bugs were found

The tests in Stage 4 found no implementation bugs, and neither did the
proofs: the implementation was written carefully, against a precise spec,
with the proofs in mind. That's typical. Most of the bug-finding came
**earlier** (Stage 1 found the NaN-threshold bug before any code existed).
What the proofs add is the step from "we looked hard and found nothing" to
"no input can cause these kinds of bug".

## 5.6 Making sure no obligation disappears

`scripts/Audit.lean` asks the kernel for every theorem's axiom
dependencies, and since this stage it also checks the **frozen obligation
list** `scripts/obligations.txt` (generated from tag `stage-3`). Every
obligation must still exist and be fully proved, so a hard theorem can't
be "fixed" by deleting it. A deliberately missing name was confirmed to
fail the audit.

## 5.7 Effort

| Layer | Lines (Lean) |
|---|---|
| Spec (`Types.lean`, `Spec/`) | 411 |
| Impl (`Impl/`) | 450 |
| Proofs (`Proofs/`, statements + proofs + helpers) | 1826 |

The proofs are about four times the size of the code they verify. That ratio
is normal, and is why formal verification gets aimed at the parts where
being wrong is expensive. Here that's the alert decision, which is exactly
the part the PRD called out.
