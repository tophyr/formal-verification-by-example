# Stage 3: The spec, machine-checked (but nothing proved yet)

> **Input:** [`02-formal-model.md`](02-formal-model.md).
> **Output:** the same model in Lean 4, in three layers, that *type-checks*.

## Why Lean

Lean 4 is both a programming language and a proof assistant: the functions
we prove things about are the functions that get compiled and run. There is
no separate "model" to drift out of sync with the code. Its JSON parser
already represents numbers as exact decimals (`mantissa × 10^-exponent`),
which is what A3 demands. The project uses only Lean core, not Mathlib, so
the whole thing builds in seconds and the trusted base stays small.

## The three layers

| Layer | Directory | Contents at this stage | Rule |
|---|---|---|---|
| **Spec** | `LakeLevel/Spec/`, `LakeLevel/Types.lean` | complete | never imports `Impl` |
| **Impl** | `LakeLevel/Impl/` | type signatures; bodies are `sorry` | |
| **Obligations** | `LakeLevel/Proofs/` | theorem *statements*; proofs are `sorry` | imports both |

The import rule stops the spec from being *defined in terms of* the
implementation. It doesn't stop the same algorithm from being written a
second time inside the spec; only review catches that (docs/02 §2.0).

`sorry` is Lean's placeholder for a missing proof: it closes any goal, and
the compiler warns every time it's used. Here it marks *exactly* what's left
to do.

## Reading guide: model → Lean

| docs/02 | Lean |
|---|---|
| ⟦⟨m, e⟩⟧ | `Dec.val` (Spec/Decimal) |
| RoundsTo | `RoundsTo`, stated over `Rat`, with no algorithm |
| DecLit, den | `DecLit`, `DecLit.den` |
| days characterization | `DayCount` (Spec/Calendar) |
| parseTs ⇔ iso | `ParsesTimestamps` |
| Latest | `Latest` (Spec/Response), quantified over indices |
| ValidResp | `ValidResp`, `RecOK` |
| Prog, World, run | `Prog`, `World`, `Prog.run` (Spec/Prog) |
| trace obligations | `Proofs/Program.lean` (`never_silently_fails` is R62) |

## What type-checking alone already bought

Having Lean accept the spec rules out a class of spec bugs prose can't
avoid: every term is defined, every quantifier ranges over a definite type,
every function is applied to the right number and kind of arguments. Writing
it also forced choices that docs/02 glossed over. For example, `Latest`
needed an explicit proof that `j < i` implies `j` is a valid index, and `ValidResp`
had to say *how* the records list corresponds to the readings list (index by
index, equal lengths).

## The audit

`scripts/Audit.lean` asks the Lean **kernel** which axioms each hand-written
theorem ultimately depends on. Anything built on `sorry` depends on
`sorryAx`. At this stage:

```
$ lake env lean scripts/Audit.lean
theorems proved from standard axioms only: 0
theorems still depending on sorry: 48
definitions still depending on sorry: 33
scripts/Audit.lean:61:0: error: audit failed
```

The audit counts only theorems in `LakeLevel.Proofs.*`. Its first draft also
counted the injectivity lemmas Lean auto-generates for every structure, and
reported "87 proved" before any proof was written. A number like that gives
false confidence, so it was fixed before this commit.

### What the audit cannot tell you

A green audit means *each theorem's statement follows from the definitions*.
It does **not** mean the statements say what the PRD meant. The only way to
close that gap ("did we prove the right thing?") is for people to read the
statements in `Proofs/`, which are this stage's main output, against
docs/01. That's why statements are kept short and phrased in the PRD's
terms.
