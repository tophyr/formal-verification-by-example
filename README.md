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
| 2 | [`docs/02-formal-model.md`](docs/02-formal-model.md) | *What are the mathematical objects and functions?* |
| 3 | [`docs/03-lean-spec.md`](docs/03-lean-spec.md), `LakeLevel/{Spec,Impl,Proofs}/` | *Can a machine type-check the spec?* |
| 4 | [`docs/04-implementation.md`](docs/04-implementation.md), `LakeLevel/Impl/`, `test/` | *Does an implementation exist, and does it pass examples?* |
| **5** | [`docs/05-proofs.md`](docs/05-proofs.md), `LakeLevel/Proofs/` | *Does the implementation meet the spec for **all** inputs?* |
| 6 | `Main.lean`, `test/` | *What's left unproven, and how do we cover it?* |

## Building

Requires [elan](https://github.com/leanprover/elan) (the Lean toolchain
manager); `lean-toolchain` pins Lean v4.35.0.

```
lake build                          # type-check everything, run the tests
lake env lean scripts/Audit.lean    # which theorems are actually proved?
```

## Current stage: 5, every obligation proved

```
$ lake env lean scripts/Audit.lean
theorems proved from standard axioms only: 139 (obligations + helper lemmas)
obligations (scripts/obligations.txt) fully proved: 48/48
theorems still depending on sorry: 0
definitions still depending on sorry: 0
```

These include, for every possible network response, clock, time zone and
ntfy outcome, the guarantee that **it never exits 0 after failing to deliver
a required alert** (`never_silently_fails`). Seven planted bugs each broke a
proof, and one of them got past the whole Stage 4 test suite.
