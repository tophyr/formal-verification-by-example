#!/usr/bin/env bash
# End-to-end tests of the real binary (verified core + trusted shell), with a
# fake curl on PATH (see test/fakebin/curl and test/curl-contract.sh).
# What this CANNOT cover: real TLS, real DNS, real hydromet/ntfy behavior,
# and real curl timeouts. See docs/06-shell-and-tcb.md.
set -euo pipefail
cd "$(dirname "$0")/.."
bin=$PWD/.lake/build/bin/lake-level
[ -x "$bin" ] || { echo "build first: lake build"; exit 1; }
fx=$PWD/test/fixtures
export PATH="$PWD/test/fakebin:$PATH" TZ=America/Chicago
pass=0 fail=0
ok()  { pass=$((pass + 1)); echo "ok   $1"; }
bad() { fail=$((fail + 1)); echo "FAIL $1"; }
eq()  { if [ "$2" == "$3" ]; then ok "$1"; else bad "$1: expected $(printf %q "$2"), got $(printf %q "$3")"; fi; }

# run NAME [env...] -- args...   → sets $out $err $rc $log
run() {
  log=$(mktemp -d); out=$log/stdout; err=$log/stderr
  local envs=()
  while [ "$1" != -- ]; do envs+=("$1"); shift; done; shift
  set +e
  env FAKE_LOG="$log" FAKE_STDOUT="$out" FAKE_GET_BODY="$fx/site3963.json" "${envs[@]}" \
    "$bin" "$@" > "$out" 2> "$err"
  rc=$?
  set -e
}
calls() { find "$log" -name "*-$1" | wc -l; }

echo "# default report"
before=$(date +%s); run -- ; after=$(date +%s)
eq "exit 0" 0 "$rc"
eq "line 1" "Mansfield Dam (Lake Travis)" "$(sed -n 1p "$out")"
eq "line 2" "  Most recent lake level: 677.58 ft (MSL)" "$(sed -n 2p "$out")"
eq "line 4" "  Full pool: 681.0 ft  (+3.42 ft from full)" "$(sed -n 4p "$out")"
l3=$(sed -n 3p "$out")
# Age checked against GNU date, independently: observed at 1792468509.
lo=$(( (before - 1792468509 + 30) / 60 )); hi=$(( (after - 1792468509 + 30) / 60 ))
if [[ "$l3" =~ ^"  Observed: 2026-10-19 10:55 PM CDT ("([0-9]+)" min ago)"$ ]] \
   && (( BASH_REMATCH[1] >= lo && BASH_REMATCH[1] <= hi )); then ok "line 3 ($l3)"; else bad "line 3: $l3 (age should be $lo..$hi)"; fi
eq "exactly 4 lines" 4 "$(wc -l < "$out")"
eq "stderr empty" "" "$(cat "$err")"
eq "one GET, no POST" "1 0" "$(calls GET.args) $(calls POST.args)"
# Positive control for the "zero curl calls" checks below: the same expression counts 1 here.
eq "total curl calls" 1 "$(find "$log" -name '*.args' | wc -l)"
eq "GET url" "https://hydromet.lcra.org/api/GetDataBySite/3963/lakelevel" "$(cat "$log"/0-GET.url)"
grep -qx 'User-Agent: lake-level/1.0' "$log/0-GET.args" && ok "User-Agent header" || bad "User-Agent header"
grep -A1 -x -- '--max-time' "$log/0-GET.args" | grep -qx 30 && ok "30 s timeout" || bad "30 s timeout"
grep -A1 -x -- '--proto' "$log/0-GET.args" | grep -qx '=https' && ok "https only" || bad "https only"

echo "# --json"
run -- --json
eq "exit 0" 0 "$rc"
j=$(python3 -c '
import json,sys; d=json.load(open(sys.argv[1]))
print(sorted(d), d["site"], d["siteNumber"], d["level_ft"], d["unit"], d["observed_utc"], d["operating_range_max_ft"])' "$out")
eq "JSON keys and values" "['level_ft', 'observed_utc', 'operating_range_max_ft', 'site', 'siteNumber', 'unit'] Mansfield Dam (Lake Travis) 3963 677.58 Head 2026-10-20T03:55:09Z 681" "$j"
eq "--json makes no tz/clock difference to the network: one GET" 1 "$(calls GET.args)"

echo "# alert delivered"
run -- --threshold 677.58 --ntfy-topic my-lake
eq "exit 0" 0 "$rc"
# Positive control: proves calls() can count a POST, so the "no POST" checks below aren't vacuous.
eq "one GET, one POST" "1 1" "$(calls GET.args) $(calls POST.args)"
eq "POST url" "https://ntfy.sh/my-lake" "$(cat "$log"/1-POST.url)"
eq "POST body" $'Mansfield Dam (Lake Travis) lake level is 677.58 ft (MSL) as of 2026-10-20T03:55:09Z.\nLevel has reached the alert threshold.' "$(cat "$log"/1-POST.body)"
for h in 'Title: Lake level alert: 677.58 ft' 'Priority: high' 'Tags: warning,ocean'; do
  grep -qxF "$h" "$log/1-POST.args" && ok "header $h" || bad "header $h"; done
eq "report fully written before POST (R52)" "$(stat -c %s "$out")" "$(cat "$log"/1-POST.stdout-bytes-before)"
eq "alert notice" "  ALERT: level >= 677.58 ft -> notified ntfy.sh/my-lake" "$(cat "$err")"

echo "# alert not delivered → never exit 0 (R62)"
for case in "FAKE_POST_STATUS=500|Error: ntfy alert failed: HTTP 500" \
            "FAKE_POST_STATUS=302|Error: ntfy alert failed: HTTP 302" \
            "FAKE_FAIL=post|Error: ntfy alert failed: curl: curl: (28) Operation timed out after 30001 milliseconds"; do
  run "${case%%|*}" -- --threshold 600
  eq "${case%%|*}: exit 1" 1 "$rc"
  eq "${case%%|*}: stderr" "${case#*|}" "$(cat "$err")"
  eq "${case%%|*}: report still printed" 4 "$(wc -l < "$out")"
done

echo "# below threshold"
run -- --threshold=677.59
eq "exit 0, no POST" "0 0" "$rc $(calls POST.args)"

echo "# usage errors: exit 2, no network at all (R3)"
for a in "--threshold nan" "--thr 685" "--ntfy-topic a/b" "--site 3963?x=1" "--json --json" "--site" "bogus"; do
  run -- $a
  eq "[$a] exit 2, zero curl calls, stdout empty" "2 0 0" "$rc $(find "$log" -name '*.args' | wc -l) $(stat -c %s "$out")"
  eq "[$a] stderr is Error line + usage line" "Error: |usage: lake-level" "$(sed -n 1p "$err" | cut -c1-7)|$(sed -n 2p "$err" | cut -c1-17)"
done
run -- --help
eq "--help: exit 0, no network, usage on stdout" "0 0 usage:" "$rc $(find "$log" -name '*.args' | wc -l) $(head -c6 "$out")"

echo "# fetch failures: exit 1, nothing on stdout, never an alert (R15)"
run FAKE_FAIL=get -- --threshold 0
eq "network: exit 1 / no stdout / no POST" "1 0 0" "$rc $(stat -c %s "$out") $(calls POST.args)"
eq "network: one-line error" "Error: curl: curl: (6) Could not resolve host: hydromet.lcra.org" "$(cat "$err")"
run FAKE_GET_STATUS=503 -- --threshold 0
eq "HTTP 503: exit 1 / no stdout / no POST" "1 0 0" "$rc $(stat -c %s "$out") $(calls POST.args)"
for f in unknown-site empty-records missing-value1 null-value1 offset-timestamp impossible-date wrong-site not-head; do
  run FAKE_GET_BODY="$fx/$f.json" -- --threshold 0
  eq "$f: exit 1 / no stdout / no POST / 1 stderr line" "1 0 0 1" "$rc $(stat -c %s "$out") $(calls POST.args) $(wc -l < "$err")"
done
printf '<html>oops</html>' > "$log/html"; run FAKE_GET_BODY="$log/html" -- --threshold 0
eq "non-JSON body: exit 1 / no POST" "1 0" "$rc $(calls POST.args)"

echo "# environment"
run TZ=Nowhere/Bogus -- ; eq "bad TZ falls back to UTC display" "  Observed: 2026-10-20 03:55 AM UTC" "$(sed -n 3p "$out" | cut -c1-35)"
run TZ=UTC FAKE_GET_BODY="$fx/no-full-no-name.json" --
eq "no siteName / no full pool: fallback name, 3 lines" "site 3963|3" "$(sed -n 1p "$out")|$(wc -l < "$out")"

run FAKE_GET_BODY="$fx/no-site-number.json" --
eq "siteNumber absent is accepted (A10)" "0 4" "$rc $(wc -l < "$out")"

echo; echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
