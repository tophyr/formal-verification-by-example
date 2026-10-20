import LakeLevel

/-!
# Stage 4 tests: examples, checked at compile time

`#guard e` fails the build unless `e` evaluates to `true`. Expected values
come from **outside the implementation**: the PRD's examples, GNU `date`,
and the decisions in the ambiguity register (docs/01). They are samples:
they show the code works on these inputs. Stage 5 shows it works on all.
-/

open LakeLevel Lean

/-! ## Decimals -/

-- A6: only plain decimal literals. Each rejected case is something Python's float() accepts.
#guard parseDec "685" == some ⟨685, 0⟩
#guard parseDec "680.5" == some ⟨6805, 1⟩
#guard parseDec "-1.25" == some ⟨-125, 2⟩
#guard parseDec "007" == some ⟨7, 0⟩
#guard ["nan", "inf", "-inf", "1e3", " 685 ", "6_85", "", "-", "1.", ".5", "+5", "--5", "1.2.3", "0x10"].all
  (parseDec · == none)

-- A5: exact comparison
#guard Dec.le ⟨685, 0⟩ ⟨68500, 2⟩ && Dec.le ⟨68500, 2⟩ ⟨685, 0⟩
#guard !Dec.le ⟨68501, 2⟩ ⟨685, 0⟩
#guard (Dec.sub ⟨6810, 1⟩ ⟨67758, 2⟩).val == (342 : Rat) / 100

-- A4: ties away from zero, on the exact value. Python gives "2.67" and "0.12" here.
#guard fixed 2 (Dec.round 2 ⟨2675, 3⟩) == "2.68"
#guard fixed 2 (Dec.round 2 ⟨-2675, 3⟩) == "-2.68"
#guard fixed 2 (Dec.round 2 ⟨125, 3⟩) == "0.13"
#guard fixed 2 (Dec.round 2 ⟨67758, 2⟩) == "677.58"
#guard fixed 1 (Dec.round 1 ⟨6810, 1⟩) == "681.0"
#guard fixed 2 5 == "0.05" && fixed 2 (-5) == "-0.05" && fixed 2 0 == "0.00" && fixed 0 0 == "0"
-- A13: never "-0.00"
#guard signed 2 (Dec.round 2 ⟨-1, 3⟩) == "+0.00"
#guard signed 2 342 == "+3.42" && signed 2 (-342) == "-3.42"

-- A12: minutes, ties away from zero
#guard roundFrac 150 60 == 3 && roundFrac (-150) 60 == -3
#guard roundFrac 29 60 == 0 && roundFrac (-29) 60 == 0 && roundFrac 31 60 == 1

/-! ## Calendar: expected values from GNU `date -u -d … +%s` -/

#guard parseTs "2026-10-20T03:55:09Z" == some 1792468509
#guard parseTs "1970-01-01T00:00:00Z" == some 0
#guard parseTs "2000-02-29T23:59:59Z" == some 951868799
#guard parseTs "2000-03-01T00:00:00Z" == some 951868800
#guard parseTs "2024-12-31T23:59:59Z" == some 1735689599
#guard parseTs "9999-12-31T23:59:59Z" == some 253402300799
#guard secs ⟨1900, 3, 1, 0, 0, 0⟩ == -2203891200
#guard minInstant == -62135596800
#guard civilOf 1792468509 == ⟨2026, 10, 20, 3, 55, 9⟩
#guard civilOf (-62135596800) == ⟨1, 1, 1, 0, 0, 0⟩
#guard civilOf 951868799 == ⟨2000, 2, 29, 23, 59, 59⟩
-- A2: strict format and real dates only
#guard [ "2026-02-29T00:00:00Z",       -- 2026 is not a leap year
         "1900-02-29T00:00:00Z",       -- 1900 is not a leap year
         "2026-10-20T24:00:00Z", "2026-10-20T23:60:00Z", "2026-10-20T23:59:60Z",
         "2026-13-01T00:00:00Z", "2026-00-01T00:00:00Z", "2026-04-31T00:00:00Z",
         "2026-10-20T03:55:09+00:00", "2026-10-20 03:55:09Z", "2026-10-20t03:55:09z",
         "2026-10-20T03:55:09.5Z", "1969-12-31T23:59:59Z", "" ].all (parseTs · == none)
#guard parseTs "2024-02-29T12:00:00Z" |>.isSome
-- R41 round trip
#guard (parseTs "2026-10-20T03:55:09Z").map (iso ∘ civilOf) == some "2026-10-20T03:55:09Z"

-- A11 / R33
#guard (List.range 24).map hour12 ==
  [(12, .am), (1, .am), (2, .am), (3, .am), (4, .am), (5, .am), (6, .am), (7, .am), (8, .am),
   (9, .am), (10, .am), (11, .am), (12, .pm), (1, .pm), (2, .pm), (3, .pm), (4, .pm), (5, .pm),
   (6, .pm), (7, .pm), (8, .pm), (9, .pm), (10, .pm), (11, .pm)]

/-! ## Selection: a tie goes to the first (A1) -/

def rd (t : Int) (m : Int) : Reading := ⟨t, ⟨m, 2⟩, ""⟩
#guard select [rd 1 10, rd 3 30, rd 2 20, rd 3 99] == some (rd 3 30)
#guard select [] == none

/-! ## Decoding real and doctored responses -/

def fx (name : String) : IO String := IO.FS.readFile s!"test/fixtures/{name}.json"

def decodes (name : String) (site : Nat := 3963) : IO (Except String (Site × Reading)) :=
  return decodeBody site (← fx name)

/-- `#eval` tests that throw on failure; they run when this file is compiled. -/
def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"FAILED: {label}")

#eval do
  let .ok (S, R) ← decodes "site3963" | throw (IO.userError "site3963 should decode")
  check "site name" (S.name == "Mansfield Dam (Lake Travis)")
  check "full pool" (S.full == some (⟨6810, 1⟩ : Dec))
  check "newest" (R == (⟨1792468509, ⟨67758, 2⟩, "2026-10-20T03:55:09Z"⟩ : Reading))
  -- PRD §5.2's own example, byte for byte. Zone/now as the OS would supply at 10:55 PM CDT + 5 min.
  check "PRD example" (humanReport S R ⟨-18000, "CDT"⟩ (1792468509 + 300) ==
    "Mansfield Dam (Lake Travis)\n" ++
    "  Most recent lake level: 677.58 ft (MSL)\n" ++
    "  Observed: 2026-10-19 10:55 PM CDT (5 min ago)\n" ++
    "  Full pool: 681.0 ft  (+3.42 ft from full)\n")
  check "future" ((humanReport S R ⟨0, "UTC"⟩ (1792468509 - 180)).endsWith
    "(3 min in the future)\n  Full pool: 681.0 ft  (+3.42 ft from full)\n")
  -- R51: the alert, byte for byte
  let cfg : Cfg := { defaultCfg with threshold := some ⟨"677", ⟨677, 0⟩⟩ }
  let expected : Request := {
    method := "POST", url := "https://ntfy.sh/csarbora",
    headers := [("Title", "Lake level alert: 677.58 ft"), ("Priority", "high"),
                ("Tags", "warning,ocean")],
    body := "Mansfield Dam (Lake Travis) lake level is 677.58 ft (MSL) as of " ++
      "2026-10-20T03:55:09Z.\nLevel has reached the alert threshold." }
  check "alert" (alertReq cfg S R == expected)

#eval do
  let .ok (_, R) ← decodes "unordered-tie" | throw (IO.userError "unordered-tie should decode")
  check "first of the tied newest wins" (R.level == (⟨11111, 2⟩ : Dec))
  let .ok (S, _) ← decodes "no-full-no-name" | throw (IO.userError "no-full-no-name should decode")
  check "fallback name" (S.name == "site 3963" && S.full == none)
  -- A10: siteNumber is optional. (Added after a proof caught a mutant these tests missed:
  -- every fixture had a siteNumber, so "reject when absent" passed the whole suite.)
  check "no siteNumber is fine" ((← decodes "no-site-number") matches .ok _)

#eval do
  for name in ["unknown-site", "empty-records", "missing-value1", "null-value1",
               "offset-timestamp", "impossible-date", "wrong-site", "not-head"] do
    match ← decodes name with
    | .ok _ => throw (IO.userError s!"FAILED: {name} should be rejected")
    | .error _ => pure ()
  check "wrong site requested" ((← decodes "site3963" 3999) matches .error _)
  check "not JSON" (decodeBody 3963 "<html>" matches .error _)

/-! ## Command line -/

#guard parseArgs [] == .ok defaultCfg
#guard parseArgs ["--help"] == .help
#guard parseArgs ["--site=3999", "--json"] == .ok { defaultCfg with site := "3999", json := true }
#guard parseArgs ["--threshold", "685", "--ntfy-topic", "my-lake"] ==
  .ok { defaultCfg with threshold := some ⟨"685", ⟨685, 0⟩⟩, topic := "my-lake" }
-- A20 / A6 / A17: each of these is accepted by the original
#guard [ ["--thr", "685"],                    -- abbreviation
         ["--site", "1", "--site", "2"],      -- repeated
         ["--threshold", "nan"],              -- NaN: the silent-no-alert bug
         ["--site", "3963?x=1"],              -- query injection
         ["--ntfy-topic", "a/b"],             -- path injection
         ["--type", "LakeLevel"], ["--site", ""], ["--site", "1234567890"],
         ["--json", "--json"], ["extra"], ["--site"] ].all fun a =>
  match parseArgs a with | .usage _ => true | _ => false

/-! ## The whole program, in hand-built worlds -/

/-- A world whose GET returns `body` and whose POST returns `postResult`.
The POST stub returns a *fixed* answer, not one derived from the request,
so it can't accidentally agree with the code under test. -/
def worldWith (body : String) (postResult : PostResult) : World :=
  { get := fun _ => .response 200 body, zone := fun _ => ⟨-18000, "CDT"⟩,
    now := 1792468509 + 300, post := fun _ => postResult }

#eval do
  let body ← fx "site3963"
  let posts (argv : List String) (pr : PostResult) :=
    ((main argv).run (worldWith body pr)).1.filter Event.isPost |>.length
  let exitOf (argv : List String) (pr : PostResult) := ((main argv).run (worldWith body pr)).2
  -- at / above / below threshold (level is 677.58)
  check "alert at equal" (posts ["--threshold", "677.58"] (.response 200) == 1)
  check "alert below"    (posts ["--threshold", "600"] (.response 200) == 1)
  check "no alert above" (posts ["--threshold", "677.59"] (.response 200) == 0)
  check "no threshold"   (posts [] (.response 200) == 0)
  -- R62, with known-wrong worlds injected: every failed delivery must exit non-zero
  check "delivered → 0"  (exitOf ["--threshold", "600"] (.response 200) == 0)
  check "HTTP 500 → 1"   (exitOf ["--threshold", "600"] (.response 500) == 1)
  check "HTTP 302 → 1"   (exitOf ["--threshold", "600"] (.response 302) == 1)
  check "network → 1"    (exitOf ["--threshold", "600"] (.failed "timeout") == 1)
  check "usage → 2"      (exitOf ["--threshold", "nan"] (.response 200) == 2)
  -- R3: usage errors never touch the network, even when the world would answer
  check "usage no net"   (((main ["--site", "x"]).run (worldWith body (.response 200))).1.all
                           (!·.isNetwork))
  -- R15: bad response → no stdout, no alert, exit 1
  let bad := worldWith (← fx "null-value1") (.response 200)
  let (tr, e) := (main ["--threshold", "0"]).run bad
  check "bad → no out/post, exit 1" (e == 1 && tr.all fun ev => !ev.isOut && !ev.isPost)
