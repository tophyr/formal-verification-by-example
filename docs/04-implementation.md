# Stage 4: An implementation that passes its tests (and proves nothing)

> **Input:** Stage 3's signatures and obligations.
> **Output:** working code in `LakeLevel/Impl/`, and compile-time tests in
> `test/Tests.lean`. All 48 theorems are still `sorry`.

Most software stops at this point, so this document records exactly what we
have here, and what we don't have yet.

## What was implemented

| Module | Approach | Chosen with proofs in mind because… |
|---|---|---|
| `Decimal` | integer cross-multiplication; `roundFrac N D = ⌊(2N+D)/2D⌋` mirrored for negatives; own digit renderer `natDigits` | only `Int`/`Nat` ops; no floats anywhere |
| `Calendar` | Hinnant's closed-form `days_from_civil` / `civil_from_days`, day 0 = 0000-03-01 | every division is by a **constant**, which `omega` can reason about |
| `Select` | a left fold that replaces only on *strictly* later | "first of the maxima" falls out of `<` vs `≤` |
| `Decode` | `Except` pipeline; `mapM` over records | strictness (A7) is just `mapM`'s short-circuit |
| `Args` | token loop with a "seen" state, then `finalize` | duplicates detected in one place (`setOpt`) |
| `Program` | builds a `Prog` value; no I/O | lets Stage 5 reason about every world |

Two implementation choices deserve a note:

- **Executable specs.** `parseTs` checks `c.Acceptable` and `finalize`
  checks `SiteSyntax` etc. by *evaluating the spec predicates* (they're
  decidable). That's legitimate, and common: where the spec is already a
  cheap check, run it. It doesn't make the obligations trivial:
  `parseTs_spec` still has to show the 20-character parser reconstructs
  exactly the civil time whose `iso` is the input.
- **`humanReport` is a template.** The argument for its correctness is that
  it's the R30 format applied to verified pieces, and the tests below check
  it against the PRD's example byte for byte.

## The tests

`#guard` and `#eval` blocks run during `lake build`; a failure fails the
build. Expected values never come from the implementation itself:

- **GNU `date`** for every epoch value (`date -u -d 2026-10-20T03:55:09Z +%s`
  → `1792468509`), and for the PRD's local-time example
  (`TZ=America/Chicago date -d @1792468509` → `2026-10-19 10:55 PM CDT`).
- **The PRD** for the report and alert text.
- **The ambiguity register** for edge cases: every input Stage 1 found the
  original accepting wrongly (`nan`, `6_85`, `--thr`, `3963?x=1`, …) is
  asserted rejected.
- **Real API data** (`test/fixtures/site3963.json`, trimmed from a live
  response) plus doctored variants (null value, offset timestamp, 2026-02-29,
  wrong site, tie for newest, …).

The whole-program tests run `main` in hand-built `World`s. The POST stub
returns a **fixed** answer rather than one computed from the request, so it
can't accidentally agree with the code under test.

### Testing the tests

To check that the tests can fail at all, four plausible bugs were planted,
one at a time, and the build had to fail for each:

| Mutation | Caught by |
|---|---|
| `select`: `<` → `≤` (last of ties wins) | `Tests.lean:77` |
| `roundFrac`: ties toward zero | `Tests.lean:30` |
| `hour12 0 = (0, AM)` | `Tests.lean:69` |
| `ok2xx` accepts any status ≥ 200 | `Tests.lean:155` (`HTTP 500 → 1`) |

## What we have, and what we don't

```
$ lake env lean scripts/Audit.lean
theorems proved from standard axioms only: 0
theorems still depending on sorry: 48
definitions still depending on sorry: 0
```

Every test passes. But a test is an **existential** claim ("there is an
input on which it works"); every obligation in `Proofs/` is a **universal**
claim ("on every input"). For example, the tests check `parseTs` on 22
strings. `parseTs_spec` covers all strings. `never_silently_fails` covers
every argument list in every world, including every HTTP status code
anyone could return. Stage 5 closes that gap.
