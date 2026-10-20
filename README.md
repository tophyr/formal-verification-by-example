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
| **1** | [`docs/01-requirements.md`](docs/01-requirements.md) | *Exactly what, testably? What did the prose leave unspecified?* |
| 2 | `docs/02-formal-model.md` | *What are the mathematical objects and functions?* |
| 3 | `LakeLevel/Spec/*.lean` | *Can a machine type-check the spec?* |
| 4 | `LakeLevel/Impl/*.lean` | *Does an implementation exist, and does it pass examples?* |
| 5 | `LakeLevel/Proofs/*.lean` | *Does the implementation meet the spec for **all** inputs?* |
| 6 | `Main.lean`, `test/` | *What's left unproven, and how do we cover it?* |

## Current stage: 1, testable requirements

Trying to write a yes/no test for every sentence of the PRD turned up **21
ambiguities**, recorded in an "ambiguity register". Two of them were real
bugs in the original implementation: a `nan` threshold silently disables
alerting, and timestamps were compared as strings. Each requirement is now
tagged with how it will be checked: **P**roved, **T**ested, **I**nspected,
or **A**ssumed.
