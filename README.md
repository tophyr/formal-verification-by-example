# formal-verification-by-example

A teaching project for formal verification. It takes a small, real program,
a command-line tool that reports the Lake Travis water level and sends an
alert when it's high, and rebuilds it in stages: from a one-page product spec
to an implementation in Lean 4 whose correctness is checked by machine.

Each stage is one git commit, tagged `stage-N`. Check out a tag to see the
project exactly as it stood at that stage:

```
git log --oneline --decorate
git checkout stage-3        # e.g. the spec in Lean, nothing proved yet
git checkout main
```

## The stages

| Stage | Read | Question it answers | What it caught |
|---|---|---|---|
| 0 | [`docs/00-prd.md`](docs/00-prd.md) | *What do we want?* (prose) | |
| 1 | [`docs/01-requirements.md`](docs/01-requirements.md) | *Exactly what, testably? What did the prose leave unspecified?* | 21 ambiguities, including a real bug in the original: `--threshold nan` silently disables alerting |
| 2 | [`docs/02-formal-model.md`](docs/02-formal-model.md) | *What are the mathematical objects?* | the architecture: a pure core that *describes* its I/O, so properties can be stated over every possible environment |
| 3 | [`docs/03-lean-spec.md`](docs/03-lean-spec.md) · `LakeLevel/{Spec,Impl,Proofs}/` | *Does a machine accept the spec?* | ill-formed spec (missing index bounds, undefined correspondences) |
| 4 | [`docs/04-implementation.md`](docs/04-implementation.md) · `LakeLevel/Impl/`, `test/Tests.lean` | *Does it work on examples?* | 4/4 planted bugs |
| 5 | [`docs/05-proofs.md`](docs/05-proofs.md) · `LakeLevel/Proofs/` | *Does it work on **all** inputs?* | 7/7 planted bugs, one of which every test missed; an over-weak spec |
| **6** | [`docs/06-shell-and-tcb.md`](docs/06-shell-and-tcb.md) · `Main.lean`, `test/*.sh` | *What's left unproven, and how is it covered?* | 5/5 planted shell bugs; a vacuous test |

The original being formalized is
[`test/original/lake_level.py`](test/original/lake_level.py), about 100
lines of Python, included unchanged. Stage 1 treats it as "what a competent
developer produced from prose like Stage 0", and Stage 6 runs it side by
side with the result.

## What is proved

48 theorems, checked by Lean's kernel, depending on no axioms beyond Lean's
standard three. Quantified over **every** command line and **every** world
(every HTTP response, clock, time zone and ntfy outcome), they include:

- `never_silently_fails`: if a threshold was given, the data was valid,
  the exact level was at or above the threshold, and the program exited 0,
  then ntfy accepted the alert. This is the formal version of the PRD's
  "should never silently fail to alert".
- `alert_iff`: an alert is attempted *if and only if* it should be.
- `report_before_alert`, `bad_fetch_behavior`, `usage_behavior`
  (no network on usage errors), `exit_codes`, `stderr_shape`.
- `decode_ok_iff`: exactly the valid responses are accepted, and the
  reading returned is the declaratively specified "most recent" one.
- Exact rational comparison and rounding (`Dec.le_iff`,
  `Dec.round_spec`, `RoundsTo.unique`), rendered numbers that read back
  exactly (`parseDec_fixed`), the Gregorian calendar by characterization
  (`days_spec`), a strict timestamp parser (`parseTs_spec`), and URL
  safety (`fetchReq_url_safe`).

## What is *not* proved

The shell (`Main.lean`, about 80 lines), curl, TLS, the Lean compiler, Lean's
JSON parser and printer, the tz database, the clock, and the honesty of
hydromet and ntfy. [`docs/06`](docs/06-shell-and-tcb.md) lists each one,
what goes wrong if it's wrong, and which test is aimed at it. Real ntfy
delivery was **not** exercised, because it publishes to a public topic; run
it yourself with `lake-level --threshold 0 --ntfy-topic <your-topic>`.

## Building and checking

Requires [elan](https://github.com/leanprover/elan) (`lean-toolchain` pins
Lean v4.35.0, core only, no Mathlib), `curl`, and `python3` (for tests only).

```
lake build                          # spec + impl + proofs + compile-time tests + binary
lake env lean scripts/Audit.lean    # kernel axiom audit; 48/48 obligations
scripts/check-all.sh                # everything: build, audit, curl contract, e2e, differential
.lake/build/bin/lake-level --help
```

```
$ .lake/build/bin/lake-level
Mansfield Dam (Lake Travis)
  Most recent lake level: 677.58 ft (MSL)
  Observed: 2026-10-19 11:30 PM CDT (1 min ago)
  Full pool: 681.0 ft  (+3.42 ft from full)
```

## Repository map

```
docs/00..06-*.md        one document per stage
LakeLevel/Types.lean    shared data types (part of the spec)
LakeLevel/Spec/         what "correct" means: predicates, no algorithms
LakeLevel/Impl/         the code that runs (pure; builds a Prog value)
LakeLevel/Proofs/       the 48 obligations and their proofs (+ *Lemmas helpers)
Main.lean               the trusted shell: interprets Prog with real I/O
scripts/Audit.lean      asks the kernel what each theorem depends on
scripts/obligations.txt the frozen obligation list (from tag stage-3)
scripts/check-all.sh    every check, in order of strength
test/Tests.lean         compile-time example tests (Stage 4)
test/fixtures/          trimmed live API response + doctored variants
test/curl-contract.sh   real curl vs. the assumptions the shell makes
test/e2e.sh             the real binary, with a fake curl on PATH
test/differential.sh    the original Python vs. this, on the same inputs
test/original/          the original Python script, unchanged
test/run_original.py    runs the original with its network calls stubbed
```

## Main lessons

1. **Most of the bug-finding happened before any code existed.** Trying to
   write a yes/no test for each PRD sentence (Stage 1) found the NaN bug,
   the string-compared timestamps, and URL injection.
2. **A spec that copies the implementation proves nothing, and no tool
   will tell you.** A copied spec type-checks, proves, and passes every
   check in this repository. Every spec here is written in a different
   style from the code it constrains (relational, characterization,
   inverse, or declarative), and that was checked by review.
3. **Describe I/O as data.** Representing it as a value (`Prog`) turned
   "inspect the code to see it never exits 0 after a failed alert" into a
   theorem over all possible worlds.
4. **Name what the proofs don't cover.** Whatever is left goes into a
   small, named trusted base, and the tests are aimed at that.
5. **Check the checkers.** The audit's first draft counted auto-generated
   lemmas as "87 proved" with no work done. An e2e counter used the wrong
   glob and made every "no POST" check vacuous. A deleted theorem would
   have turned the audit green. Each was caught by asking "could this pass
   while being wrong?" and then trying to make it do so.
