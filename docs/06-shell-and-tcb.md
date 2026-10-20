# Stage 6: The shell, the trusted base, and what's still not covered

> **Input:** a verified pure core (Stage 5).
> **Output:** a runnable binary; an explicit, audited list of everything the
> proofs *assume*; and tests aimed at that list.

## 6.1 The shell

`Main.lean` is the only code that touches the outside world. It's an
interpreter for `Prog`, with one line per constructor:

```lean
partial def interp : Prog → IO UInt32
  | .done e => return e.toUInt32
  | .get r k => do interp (k (← httpGet r))
  | .zoneAt t k => do interp (k (← zoneAt t))
  | .clock k => do interp (k (← now))
  | .out s k => do IO.print s; (← IO.getStdout).flush; interp k
  | .err s k => do IO.eprint s; (← IO.getStderr).flush; interp k
  | .post r k => do interp (k (← httpPost r))
```

Plus `httpGet`/`httpPost` (run `curl`, split off the status line),
`zoneAt` (ask Std.Time's tz database), and `now`. About 80 lines in all,
and **it makes no decisions**: what to fetch, what to print, whether to
alert, and which exit status to return were all decided inside the verified
`LakeLevel.main`.

## 6.2 The trusted computing base (TCB)

Everything the proofs rely on but don't check, audited against the final
code:

| # | Trusted component | What could go wrong if it's wrong | Mitigation here |
|---|---|---|---|
| 1 | **Lean kernel** + axioms `propext`, `Quot.sound`, `Classical.choice` | a false theorem is accepted | industry-standard foundation; audit confirms nothing else is used |
| 2 | **Lean compiler** (Lean → C → native) | the binary doesn't behave like the definitions that were proved | e2e + differential tests run the *binary* |
| 3 | `Lean.Json.parse` | a body is decoded to a different JSON value than it denotes | fixtures from real responses; tests |
| 4 | `Lean.Json.pretty` (JSON output text) | `--json` text doesn't denote `jsonReport` | e2e parses the output with Python's `json` |
| 5 | `toString` on `Nat`, `s!` interpolation | the `site N` fallback name or an error message is mis-rendered | not decision-relevant; tests |
| 6 | **`Main.lean`** (the shell) | wrong primitive for a constructor; status mis-parsed | small enough to read; e2e with fake curl; 5/5 shell mutations caught |
| 7 | **curl** | doesn't send what we built, mis-reports status, ignores `--max-time` | `test/curl-contract.sh` checks the exact flags against real curl |
| 8 | TLS, DNS, the network | spoofed or tampered data | `--proto =https`; curl's certificate validation |
| 9 | hydromet.lcra.org | sends wrong numbers | out of scope. No software can verify its inputs are true |
| 10 | ntfy.sh | 2xx returned but notification not delivered | out of scope |
| 11 | tz database, system clock | wrong local time or age | display only: neither can change the level, the alert decision, or the exit status |

### Why row 6 matters most

A concrete example of where the proofs stop. `never_silently_fails` (R62)
proves: *in every world, if the alert condition held and the world says the
POST got a 2xx, then …*. It's about **the world the shell reports**. If
`httpPost` had a bug and returned `.response 200` for every POST, every theorem
would still be true, and the tool would silently fail to alert. So that
exact mutation was tried against the e2e suite. It was caught: 7 checks
failed, including `HTTP 500 → exit 1`.

> Whatever the proofs don't cover is concentrated in a small, named place,
> and that's where the tests are aimed.

## 6.3 The tests that cover the TCB

| Script | Covers TCB rows | What it does |
|---|---|---|
| `test/curl-contract.sh` | 7 | Runs **real** curl, with Main.lean's exact flags, against a local server. Checks stdout is exactly `\n200`; non-2xx still exits 0 with the code; body bytes and newlines survive stdin; `--header User-Agent` replaces curl's default; a refused connection exits non-zero with a message; `--proto =https` refuses http. |
| `test/e2e.sh` | 2, 4, 6 | Runs the **real binary** with a fake `curl` on `PATH`. The fake reproduces exactly the contract above (so it can't drift from real curl unnoticed) and logs every call. 65 checks. Age is checked against GNU `date`. R52 is checked at run time: the fake records how many bytes of stdout existed when the POST arrived. |
| `test/differential.sh` | 2, 3 | Runs the **original Python** and this binary on the same fixtures, side by side. |

### Tests of the tests

- Each "no POST happened" check in e2e is paired with a positive control
  showing the same counter reads 1 when a POST does happen. The first draft
  of the counter used the wrong filename glob and returned 0 for
  everything, so every "no POST" check passed vacuously. The positive
  control is what caught it.
- Five shell mutations, all caught:

  | Mutation of `Main.lean` | Checks failed |
  |---|---|
  | report every POST as HTTP 200 | 7 (incl. `HTTP 500 → exit 1`) |
  | write stderr to stdout | 34 |
  | drop `--max-time 30` | 4 |
  | never print the report | 5 |
  | drop `--proto =https` | 4 |

## 6.4 Differential results vs. the original

Every difference is an ambiguity-register decision, and four of them are
defects in the original:

| Input | Original | This | Register |
|---|---|---|---|
| real response, all modes | exit 0 | exit 0; identical text, numerically identical JSON (`681` vs `681.0`, A14) | |
| 2-way tie for newest | first tied | first tied | A1 (same) |
| non-newest record has `value1: null` / missing | **exit 0, silently ignores it** | exit 1 | A7 |
| newest record has `value1: null` | uncaught `TypeError` traceback | exit 1, one `Error:` line | A7, A18 |
| a timestamp with `+00:00` offset | exit 0 (string-compared) | exit 1 | A1, A2 |
| `2026-02-29T…` | exit 0 | exit 1 | A2 |
| `siteNumber` ≠ requested | exit 0, **reports the other site** | exit 1 | A10 |
| `value1Type: "Stage"` | exit 0, **reports stage as lake level** | exit 1 | A9 |
| unknown site (live shape) | exit 1 | exit 1 (caught earlier, as not-Head) | A8, A9 |
| `--threshold nan` | **exit 0, never alerts** | exit 2 | A6 |

## 6.5 What is still not covered

- **Real ntfy delivery was not exercised.** POSTing to ntfy.sh publishes a
  notification on a public topic, so it was left for the owner to run:
  `lake-level --threshold 0 --ntfy-topic <your-topic>`.
- **curl's 30 s timeout firing** was not tested end to end. The flag's
  presence is tested (e2e), and that curl honors it is assumed (TCB row 7).
- **TLS certificate validation** is curl's default; not tested here.
- **Compiler correctness** (TCB row 2) is covered only by tests of the
  binary, not by proof. Verified compilation (as in CompCert or CakeML)
  is the research answer; Lean doesn't offer it.
- The **template equations** (exact report and alert text) are proved only
  in the weak sense of Stage 2 §2.0. Their correctness rests on review
  against the PRD and the byte-for-byte tests.
