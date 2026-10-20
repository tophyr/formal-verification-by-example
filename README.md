# formal-verification-by-example

A teaching project for formal verification. It takes a small, real program,
a command-line tool that reports the Lake Travis water level and sends an
alert when it's high, and rebuilds it in stages: from a one-page product spec
to an implementation in Lean 4 whose correctness is checked by machine.

Each stage is one git commit, tagged `stage-N`. Check out a tag to see the
project exactly as it stood at that stage:

```
git checkout stage-0     # just the PRD
git log --oneline --decorate
```

## The stages

| Stage | Artifact | Question it answers |
|---|---|---|
| 0 | [`docs/00-prd.md`](docs/00-prd.md) | *What do we want?* (prose) |
| 1 | [`docs/01-requirements.md`](docs/01-requirements.md) | *Exactly what, testably? What did the prose leave unspecified?* |
| **2** | [`docs/02-formal-model.md`](docs/02-formal-model.md) | *What are the mathematical objects and functions?* |
| 3 | `LakeLevel/Spec/*.lean` | *Can a machine type-check the spec?* |
| 4 | `LakeLevel/Impl/*.lean` | *Does an implementation exist, and does it pass examples?* |
| 5 | `LakeLevel/Proofs/*.lean` | *Does the implementation meet the spec for **all** inputs?* |
| 6 | `Main.lean`, `test/` | *What's left unproven, and how do we cover it?* |

## Current stage: 2, the formal model

The requirements become mathematical objects: exact decimals (`ℤ × ℕ`), a
*relational* spec of rounding, a calendar specified by *characterization*
(`days(epoch) = 0`, `days(next d) = days d + 1`) rather than by a formula,
and a declarative spec of "most recent". The most important decision is to
model the whole program as a *data structure that describes its I/O*, so
that properties like "never exit 0 after failing to alert" can be stated
for **every possible environment**.

Stage 1 found one real bug (a `nan` threshold silently disables alerting)
and one latent one (timestamps compared as strings, which works only
because the API happens to use a single format).
