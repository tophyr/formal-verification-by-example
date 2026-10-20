# Stage 1: Testable requirements and the ambiguity register

> **Input:** [`00-prd.md`](00-prd.md) (prose).
> **Output:** a numbered list of atomic requirements, each of which can be
> checked yes/no; and a register of every question the prose left
> unanswered or ambiguous, with the decision we made.

## 1.1 What this stage is for

A PRD is written to *communicate intent* to a human who shares your context.
A requirement is written so that a *stranger* can decide, for a given run of
the program, whether it complied. The method here is mechanical:

1. **Atomize.** Split every sentence into claims that are individually
   true/false. "Print the level to two decimal places, when it was observed,
   and how long ago" is at least three requirements.
2. **Try to write the test.** For each atomic claim, attempt to write down the
   exact input and exact expected output. Each time you can't, because the
   prose doesn't say, you've found an **ambiguity**.
3. **Decide, and write the decision down.** Every ambiguity gets an explicit
   resolution and a rationale. By the end of this stage, no question is left
   open.
4. **Tag each requirement with how it will be verified.** This is the first
   time the question "which parts can be *proved*?" gets asked.

### Verification-method tags

| Tag | Meaning | Strength |
|---|---|---|
| **P** | *Proved*: a machine-checked theorem over **all** inputs (Stage 5) | strongest |
| **T** | *Tested*: specific executions checked automatically (Stage 4/6) | samples only |
| **I** | *Inspected*: a human reads a small piece of trusted code | judgment |
| **A** | *Assumed*: a property of the environment we rely on but do not check | none; the trust is documented |

The practical goal of formal verification is to push as many requirements
as possible into **P**, keep the **I** and **A** requirements few and
explicit, and know exactly what they are.

### Evidence: the original implementation

The original, [`test/original/lake_level.py`](../test/original/lake_level.py),
is in effect what a competent developer produced from prose like Stage 0.
Where the PRD is ambiguous, the register below records what that
implementation actually did. Every such claim was checked by running Python 3,
not from memory.

---

## 1.2 Ambiguity register

Each entry: the PRD text → the question it fails to answer → what the
original did → **decision**.

### A1. "picks the most recent reading": by what, and what about ties?
- *Question:* Most recent by what ordering? What if two readings share the
  newest timestamp?
- *Original:* `max(records, key=lambda r: r["dateTime"])`, which compares
  the timestamp **strings** lexicographically. Ties: first maximum in list order.
- *Problem found:* String order equals time order only if every timestamp is
  in the same zone and fixed-width format. Verified:
  `max("2026-10-20T04:00:00-05:00", "2026-10-20T08:00:00Z")` returns the
  `08:00Z` string, although `04:00-05:00` is `09:00Z`, the *later* instant.
- **Decision:** Order readings by the **instant** they denote (parsed, not
  textual). Among readings tied for the latest instant, choose the one that
  appears **first** in the API's list. (A4 makes the string-order bug
  unreachable anyway, but the requirement is stated about instants.)

### A2. What timestamp formats are accepted?
- *Observed:* All 4306 records in a live sample are exactly
  `YYYY-MM-DDTHH:MM:SSZ` (UTC, no fractional seconds).
- **Decision:** Accept **only** that format, with fields in calendar range
  (month 01–12, day valid for the month in the proleptic Gregorian calendar
  including leap years, hour 00–23, minute 00–59, second 00–59) and year
  1970–9999. Leap seconds (`:60`) are rejected. Anything else makes the
  record malformed (→ A7).

### A3. What kind of number is a "level"?
- *Original:* IEEE-754 binary float.
- *Problem found:* the PRD demands it "never report a wrong level", but
  binary floats cannot represent `677.58` exactly, and float formatting
  produces surprises (see A4).
- **Decision:** A level is an **exact decimal**: the rational number written
  in the JSON text. All comparisons and arithmetic are exact.

### A4. "two decimal places": rounded how?
- *Original:* Python `f"{x:.2f}"` on a binary float. Verified:
  `2.675 → "2.67"`, `0.125 → "0.12"`, `0.375 → "0.38"`. The result depends on
  the binary approximation, not on the decimal value the API sent.
- **Decision:** Round the exact decimal value to the nearest multiple of
  10⁻ⁿ, **ties away from zero** (so `2.675 → 2.68`, `-2.675 → -2.68`). This
  rule is used everywhere rounding occurs (levels, full pool, differences,
  minutes). In practice the API sends ≤ 2 decimals, so levels display
  exactly; but the requirement must say what happens otherwise.

### A5. "at or above the threshold": compared against what?
- *Question:* The exact level, or the displayed (rounded) level? E.g. level
  684.996, threshold 685: display shows `685.00`.
- **Decision:** Compare the **exact** level with the **exact** threshold:
  alert ⇔ `level ≥ threshold`. Consequence, accepted: the text may show
  `685.00` without alerting at 685. (Unreachable with 2-decimal data.)

### A6. What is a valid `--threshold`?
- *Original:* Python `float()`. Verified it accepts `nan`, `inf`, `-inf`,
  `1e3`, `" 685 "`, and `6_85` (= 685.0).
- *Problem found:* `--threshold nan` is accepted, and `level >= nan` is
  always false: **the tool silently never alerts.** This directly violates
  PRD §6 ("never silently fail to alert").
- **Decision:** A threshold is `-?[0-9]+(\.[0-9]+)?` exactly. Anything else is
  a usage error (A20).

### A7. What if a record is malformed?
- *Question:* missing `dateTime` or `value1`; `value1` null or a string; a bad
  timestamp.
- *Original (verified by running it against doctored responses):* a record
  missing `dateTime` → `Error: 'dateTime'`, exit 1, wherever it is in the
  list (the `max` that picks the newest runs inside the `try`). Everything
  else is read only from the newest record. There, missing `value1` →
  uncaught `KeyError` traceback; `value1: null` → uncaught `TypeError`
  traceback; an impossible date → uncaught `ValueError` traceback. In any
  other record, the same defects are never read: the original prints its
  report, alerts if the level is high, and exits 0 without mentioning the
  corrupt data. None of these behaviors is specified.
- **Decision:** **Strict.** If *any* record is malformed, the whole response
  is rejected with an error (exit 1). Rationale: a response with corrupted
  records is evidence the data is not what we think it is, and PRD §6 ranks
  "never report a wrong level" above availability. Fields other than
  `dateTime` and `value1` (e.g. `value2`) are ignored.

### A8. "no readings"
- *Observed:* An unknown site (`999999`) returns **HTTP 200** with
  `"records": []` and a placeholder name (`"Test Rain Test"`), not a 404.
- **Decision:** missing `records`, non-array `records`, and empty `records`
  are all errors (exit 1).

### A9. Is this even lake level data?
- *PRD:* "`value1` is the lake level (because `value1Type` is `"Head"`)."
- *Observed:* the unknown-site response has `"value1Type": "Stage"`.
- *Original:* never checks; JSON `unit` defaults to `"Head"` if absent.
- **Decision:** `value1Type` must be present and equal to `"Head"`;
  otherwise error. The JSON `unit` field is therefore always `"Head"`
  (kept for compatibility with the PRD's schema).

### A10. Whose site is this?
- *Question:* What if the response's `siteNumber` differs from the requested
  site?
- **Decision:** If `siteNumber` is present it must be an integer equal to the
  requested site number; otherwise error (we fetched the wrong thing). If
  absent, the requested number is used. `siteName` absent → `site {N}`
  (as original).

### A11. "in the user's local time"
- *Question:* Which zone; which UTC offset (DST changes it); what format?
- *Original:* `astimezone()` (the process's `TZ` / system zone, at the
  observed instant), then `%Y-%m-%d %I:%M %p %Z`.
- **Decision:** Use the process's local zone **as of the observed instant**.
  Format `YYYY-MM-DD hh:MM AM|PM ZZZ`: 12-hour clock, two-digit hour
  `01`–`12` (00:xx is `12:xx AM`, 12:xx is `12:xx PM`), seconds **truncated**
  (not rounded), zone abbreviation from the tz database. The offset and
  abbreviation come from the OS (**A**-tagged: we trust the tz database).

### A12. "how long ago that was"
- *Original:* `f"{minutes:.0f}"` on float minutes, which rounds half to **even**
  (verified: `2.5 → "2"`, `3.5 → "4"`), and a future timestamp prints
  `"-0 min ago"` or `"-3 min ago"`.
- **Decision:** `age = round((now − observed) / 60 s)` with A4's rule.
  If `age ≥ 0`: `(N min ago)`. If `age < 0` (clock skew; observation in the
  future): `(N min in the future)` with `N = |age|`. Never `-0`.

### A13. Full pool: "if the site reports a full-pool level"
- *Original:* `if max_ft:`, so a full pool of `0.0` is treated as absent
  (verified `bool(0.0) is False`). The difference is formatted `+.2f` and
  can print `-0.00` (verified for `-0.001`).
- **Decision:** Line shown iff `lakeOperatingRangeMax` is present and a
  number (zero included). Full pool shown with 1 decimal; difference
  `full − level` computed **exactly**, then rounded to 2 decimals, with an
  explicit sign; a difference that rounds to zero is `+0.00`. If
  `lakeOperatingRangeMax` is present but not a number (or null), it is
  treated as absent.

### A14. JSON output: exact number text? key order? `observed_utc` form?
- **Decision:** Keys are exactly `site, siteNumber, level_ft, unit,
  observed_utc, operating_range_max_ft`. JSON object member order is not
  significant (RFC 8259 §4) and is **unspecified**. `level_ft` and
  `operating_range_max_ft` are JSON numbers **numerically equal** to the
  input decimals (textual form may differ, e.g. `681.0` vs `681`).
  `observed_utc` is the canonical `YYYY-MM-DDTHH:MM:SSZ` rendering of the
  instant, which, given A2, is byte-identical to the input string.

### A15. Alert content
- **Decision:** `{level}` in title and body is A4-rounded to 2 decimals.
  `{observation time}` is the UTC `YYYY-MM-DDTHH:MM:SSZ` string. Body is
  exactly line 1 `"\n"` line 2, no trailing newline (as original).

### A16. Ordering of output vs alert; what counts as delivered
- **Decision:** The report (text or JSON) is written to stdout **before** the
  alert is attempted. The alert is delivered iff ntfy returns HTTP 2xx. On a
  failed alert, stdout already holds the report and the exit status is 1.

### A17. What may be put in a URL?
- *Original:* `--site`, `--type`, `--ntfy-topic` are pasted into URLs
  unchecked. `--site '3963?x=1'` changes the query string; `--ntfy-topic
  'a/b'` posts to a different path.
- **Decision:** site = `[0-9]{1,9}`; type = `[a-z]{1,32}`;
  topic = `^[-_A-Za-z0-9]{1,64}$` (verified against ntfy's own `topicRegex`
  in `server/server.go`). Anything else is a usage error.

### A18. Errors: what is "a one-line error message"?
- **Decision:** Exactly one line on stderr: `Error: ` + message + `\n`, where
  the message contains no newline (any newline from an underlying error is
  replaced by a space). Nothing is written to stdout on an error that occurs
  before the report.

### A19. Exit statuses
- **Decision:** `0` success (whether or not an alert was sent); `1` runtime
  error (network, response, alert delivery); `2` usage error (as argparse).

### A20. Command-line syntax details
- *Original:* argparse; verified it accepts abbreviations (`--thr 685` means
  `--threshold`) and repeated options (last wins).
- **Decision:** Accept `--opt VALUE` and `--opt=VALUE`; no abbreviations; an
  option given twice is a usage error; unknown options and positional
  arguments are usage errors; `--help` prints usage to stdout and exits 0.
  Usage errors print `Error: ` + message and the usage line to stderr.

### A21. HTTP details
- **Decision:** One GET, `User-Agent: lake-level/1.0`, 30 s total timeout.
  Non-2xx status, unparseable body, or a non-object top-level value are
  errors. No retries. (Timeout and transport are **A**/**I**-tagged.)

---

## 1.3 Requirements

Notation: *the response* is the decoded JSON body; *a valid response* is one
satisfying R10–R16. Each requirement ends with its verification tag and the
ambiguity entries / PRD sections it came from.

### Command line
- **R1** The tool shall accept the options `--site`, `--type`, `--json`,
  `--threshold`, `--ntfy-topic`, `--help` with the defaults of PRD §5.5.
  **[P]** (PRD §5.5)
- **R2** The tool shall reject, as a usage error, any argument list not
  conforming to A20, and any `--site`/`--type`/`--ntfy-topic`/`--threshold`
  value not matching A17/A6. **[P]** (A6, A17, A20)
- **R3** On a usage error, the tool shall make no network request. **[P]+[I]**

### Fetching
- **R4** The tool shall issue exactly one GET to
  `https://hydromet.lcra.org/api/GetDataBySite/{site}/{type}` with
  `User-Agent: lake-level/1.0`. **[P]** for the URL/headers value, **[I]** for
  its transmission. (PRD §4)
- **R5** The request shall time out after 30 s, which shall be an error.
  **[A]+[T]** (A21)
- **R6** The URL shall contain no characters other than those of the fixed
  prefix, digits, lowercase letters and `/`. **[P]** (A17)

### Validating the response
- **R10** The top level shall be a JSON object. **[P]** (A21)
- **R11** `value1Type` shall equal `"Head"`. **[P]** (A9)
- **R12** If present, `siteNumber` shall equal the requested site. **[P]** (A10)
- **R13** `records` shall be a non-empty array. **[P]** (A8)
- **R14** Every record shall have a `dateTime` string in the A2 format and a
  numeric `value1`. **[P]** (A2, A7)
- **R15** If any of R10–R14 fails, the tool shall report an error and exit 1,
  and shall neither print a report nor send an alert. **[P]** (A7, §5.6)
- **R16** The tool shall parse numbers exactly (no rounding on input). **[P]**
  modulo the JSON parser (**A**). (A3)

### Selecting the reading
- **R20** The selected reading shall be an element of `records`. **[P]**
- **R21** No record shall denote a later instant than the selected one.
  **[P]** (A1)
- **R22** Among records tied for the latest instant, the selected one shall
  be the first in list order. **[P]** (A1)
- **R23** The selected reading's instant shall be computed from its
  timestamp by the proleptic Gregorian calendar, with
  `1970-01-01T00:00:00Z` = 0 and each valid second one more than the
  previous. **[P]** (A2)

### Human-readable report (default)
- **R30** stdout shall be exactly these lines, each ending `\n`:
  1. `{siteName}`
  2. `  Most recent lake level: {level, 2dp} ft (MSL)`
  3. `  Observed: {local time per A11} ({age per A12})`
  4. *(iff full pool present, A13)* `  Full pool: {full, 1dp} ft  ({full−level, signed 2dp} ft from full)`

  **[P]** for the string given its inputs (PRD §5.2)
- **R31** Decimal rendering to *n* places shall round per A4 and print
  exactly *n* fractional digits, a leading `-` iff the rounded value is
  negative, and no leading zeros except a single `0` before the point.
  **[P]** (A4)
- **R32** Signed rendering shall prefix `+` iff the rounded value is ≥ 0.
  **[P]** (A13)
- **R33** The 12-hour clock rendering shall be a bijection from hours
  0–23 to `{01..12} × {AM, PM}` with 0 ↦ `12 AM`, 12 ↦ `12 PM`. **[P]** (A11)
- **R34** Local civil time shall be the civil time of
  `instant + offset`, with `offset` and abbreviation supplied by the OS for
  that instant. **[P]** for the conversion, **[A]** for the offset. (A11)
- **R35** "now" shall be the system wall clock. **[A]** (A12)

### JSON report (`--json`)
- **R40** stdout shall be one JSON object with exactly the keys of A14, whose
  values are: `site` = siteName (or fallback), `siteNumber` = the site
  number, `level_ft` = the exact level, `unit` = `"Head"`, `observed_utc` =
  canonical UTC string, `operating_range_max_ft` = full pool or `null`.
  **[P]** for the JSON value, **[A]** for Lean's JSON printer. (A14)
- **R41** Rendering then re-parsing a valid timestamp shall yield the same
  string (so `observed_utc` equals the input). **[P]** (A14)

### Alerting
- **R50** An alert shall be attempted **if and only if** a threshold was
  given, the response is valid, and `level ≥ threshold` exactly. **[P]**
  (A5, §5.4)
- **R51** The alert request shall be a POST to `https://ntfy.sh/{topic}`
  with headers `Title: Lake level alert: {level 2dp} ft`, `Priority: high`,
  `Tags: warning,ocean`, and body
  `{name} lake level is {level 2dp} ft (MSL) as of {utc}.\nLevel has reached the alert threshold.`
  **[P]** for the request value, **[I]** for transmission. (A15)
- **R52** The alert shall be attempted only after the report is written.
  **[I]** (A16)
- **R53** An alert is delivered iff ntfy answers 2xx. On delivery the tool
  shall write `  ALERT: level >= {threshold as typed} ft -> notified ntfy.sh/{topic}` to stderr. **[I]+[T]** (A16)
- **R54** On non-delivery the tool shall report an error and exit 1. **[P]**
  for the exit-status logic, **[I]** for detection. (A16, §6)

### Errors & exit status
- **R60** Every error shall produce exactly one stderr line `Error: {msg}`
  with no newline inside `msg` (plus the usage line, for usage errors).
  **[P]** (A18)
- **R61** Exit status shall be 0 on success, 1 on runtime error, 2 on usage
  error. **[P]** (A19)
- **R62** If the run is not a success, the exit status shall be non-zero.
  In particular, there shall be no outcome in which a threshold was given,
  the level was ≥ threshold, no alert was delivered, and the exit status
  is 0. **[P]** (PRD §6 "never silently fail to alert")

### Non-functional
- **R70** Runtime < 5 s on a normal connection. **[T]** (§6)
- **R71** Single executable; runtime dependencies: `curl` and the system tz
  database. **[I]** (§6)

---

## 1.4 Tally

| Tag | Count (primary) | What it means for the design |
|---|---|---|
| P | most | must live in a **pure, total** core with no I/O |
| I | R3, R4, R51–R54 (transmission parts) | the I/O shell must be **tiny** enough to read |
| A | JSON parser, tz database, clock, curl, TLS, Lean compiler/kernel | the **trusted computing base**, listed in Stage 6 |
| T | R5, R53, R70 | end-to-end tests |

The tally already shapes the architecture: a **functional core** that takes
everything the outside world supplies (arguments, response body, current
time, UTC offset, alert outcome) as *plain data* and returns everything the
outside world should do (what to print, what to send, what exit code) as
plain data, and a thin **imperative shell** that only moves bytes. Stage 2
designs it.

## 1.5 Notes on what changed vs. the PRD

Two decisions (A6 and R62) do more than clarify the PRD. They fix a real
defect in the original: a NaN threshold silently disables alerts. A third (A1)
replaces an implementation that was only accidentally correct. These were
found only by trying to state the requirement precisely enough to test.
This is the cheapest bug-finding that formal methods offer, and it happens
before any verified code exists.
