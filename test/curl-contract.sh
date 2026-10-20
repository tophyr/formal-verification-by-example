#!/usr/bin/env bash
# Contract test: the shell (Main.lean) and the fake curl (test/fakebin/curl)
# both assume how the REAL curl behaves with the exact flags Main.lean passes.
# This checks those assumptions against real curl and a local server, so the
# fake can't silently drift from reality. Prints FAIL and exits 1 on mismatch.
set -euo pipefail
cd "$(dirname "$0")"
tmp=$(mktemp -d); trap 'kill $srv 2>/dev/null || true; rm -rf "$tmp"' EXIT
port=$((20000 + RANDOM % 20000))
python3 contract_server.py "$port" "$tmp/got" & srv=$!
for _ in $(seq 50); do curl -s -o /dev/null "http://127.0.0.1:$port/" && break; sleep 0.1; done

fail=0
check() { if [ "$2" == "$3" ]; then echo "ok   $1"; else echo "FAIL $1: expected $(printf %q "$2"), got $(printf %q "$3")"; fail=1; fi; }
# Same flags as Main.lean's curlBase, minus --proto =https (the local server is plain http).
base=(--silent --show-error --max-time 30 --write-out $'\n%{http_code}')

body=$'Site lake level is 677.58 ft (MSL) as of 2026-10-20T03:55:09Z.\nLevel has reached the alert threshold.'
for code in 200 500; do
  out=$(printf '%s' "$body" | curl "${base[@]}" --request POST --header 'Title: t' \
        --data-binary @- --output /dev/null -- "http://127.0.0.1:$port/$code"; echo "|rc=$?")
  check "POST $code: stdout is exactly \\n$code, curl exits 0" $'\n'"$code|rc=0" "$out"
done
got=$(cat "$tmp/got.body")
check "POST body arrives byte-identical (newline preserved)" "$body" "$got"

out=$(curl "${base[@]}" --request GET --header 'User-Agent: lake-level/1.0' -- "http://127.0.0.1:$port/404"; echo "|rc=$?")
check "GET: body, \\n, status as the last line, curl exits 0" $'line1\nline2\n404|rc=0' "$out"
ua=$(grep -i '^User-Agent:' "$tmp/got.headers" | tr -d '\r')
check "--header User-Agent replaces curl's default" "User-Agent: lake-level/1.0" "$ua"

set +e; err=$(curl "${base[@]}" --max-time 2 -- "http://127.0.0.1:1/" 2>&1 >/dev/null); rc=$?; set -e
check "refused connection: curl exits 7" "7" "$rc"
case "$err" in curl:*) echo "ok   refused connection: message on stderr";; *) echo "FAIL stderr: $err"; fail=1;; esac

set +e; curl --silent --proto =https -- "http://127.0.0.1:$port/" >/dev/null 2>&1; rc=$?; set -e
check "--proto =https refuses plain http (exit 1)" "1" "$rc"
exit $fail
