#!/usr/bin/env bash
# Differential test: original Python vs. this implementation, same inputs.
# Every difference must be one the ambiguity register (docs/01) decided on
# purpose; anything else is a bug in one of them. Prints a markdown table.
# The original is test/original/lake_level.py, run by test/run_original.py.
set -uo pipefail
cd "$(dirname "$0")/.."
bin=$PWD/.lake/build/bin/lake-level
export PATH="$PWD/test/fakebin:$PATH" TZ=America/Chicago
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
# Ages differ between two runs a moment apart; mask them.
mask() { sed -E 's/\([0-9]+ min (ago|in the future)\)/(N min ago)/'; }
norm_json() { python3 -c 'import json,sys
try: print(json.dumps(json.load(sys.stdin, parse_int=float), sort_keys=True))  # 681 == 681.0 (A14)
except Exception: print("<not json>")'; }

echo "| fixture | args | original | this | stdout |"
echo "|---|---|---|---|---|"
for f in site3963 unordered-tie no-full-no-name unknown-site empty-records missing-value1 null-value1 \
         offset-timestamp impossible-date wrong-site not-head; do
  for args in "" "--json" "--threshold 600"; do
    python3 test/run_original.py "test/fixtures/$f.json" $args > "$tmp/po" 2> "$tmp/pe"; prc=$?
    mkdir -p "$tmp/log"; rm -f "$tmp/log"/*
    FAKE_LOG="$tmp/log" FAKE_GET_BODY="test/fixtures/$f.json" "$bin" $args > "$tmp/lo" 2> "$tmp/le"; lrc=$?
    if [ "$args" = --json ]; then a=$(norm_json < "$tmp/po"); b=$(norm_json < "$tmp/lo")
    else a=$(mask < "$tmp/po"); b=$(mask < "$tmp/lo"); fi
    if [ "$a" == "$b" ]; then same=same; else same="**differs**"; fi
    perr=$(tail -1 "$tmp/pe" | cut -c1-40); lerr=$(head -1 "$tmp/le" | cut -c1-40)
    echo "| $f | \`${args:-—}\` | exit $prc${perr:+ · $perr} | exit $lrc${lerr:+ · $lerr} | $same |"
  done
done
