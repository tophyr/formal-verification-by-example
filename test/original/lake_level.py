#!/usr/bin/env python3
"""Report the most recent LCRA Lake Level for a given hydromet site.

The LCRA charts page (hydromet.lcra.org/Charts) loads its data from a JSON
API that the page's own JavaScript calls. We hit that API directly instead
of scraping the rendered chart.

Default site 3963 is Mansfield Dam (Lake Travis).
"""

import argparse
import json
import sys
import urllib.request
from datetime import datetime, timezone

API = "https://hydromet.lcra.org/api/GetDataBySite/{site}/{type}"


def fetch(site, site_type):
    url = API.format(site=site, type=site_type)
    req = urllib.request.Request(url, headers={"User-Agent": "lake-level/1.0"})
    with urllib.request.urlopen(req, timeout=30) as resp:
        return json.load(resp)


def notify(topic, level, name, observed):
    """POST a warning to an ntfy.sh topic."""
    body = (
        f"{name} lake level is {level:.2f} ft (MSL) as of {observed}.\n"
        f"Level has reached the alert threshold."
    ).encode("utf-8")
    req = urllib.request.Request(
        f"https://ntfy.sh/{topic}",
        data=body,
        headers={
            "Title": f"Lake level alert: {level:.2f} ft",
            "Priority": "high",
            "Tags": "warning,ocean",
        },
    )
    with urllib.request.urlopen(req, timeout=30) as resp:
        return resp.status


def most_recent(data):
    records = data.get("records") or []
    if not records:
        raise ValueError("API returned no records")
    # Records come newest-first, but sort defensively by timestamp.
    return max(records, key=lambda r: r["dateTime"])


def main():
    p = argparse.ArgumentParser(description="Report the most recent LCRA lake level.")
    p.add_argument("--site", default="3963", help="LCRA site number (default: 3963, Lake Travis)")
    p.add_argument("--type", default="lakelevel", help="Site type (default: lakelevel)")
    p.add_argument("--json", action="store_true", help="Emit machine-readable JSON")
    p.add_argument("--threshold", type=float,
                   help="If set, POST an ntfy alert when level >= this value (ft)")
    p.add_argument("--ntfy-topic", default="csarbora",
                   help="ntfy.sh topic to POST alerts to (default: csarbora)")
    args = p.parse_args()

    try:
        data = fetch(args.site, args.type)
        rec = most_recent(data)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1

    level = rec["value1"]  # value1Type == "Head" == the lake level in feet MSL
    ts = datetime.fromisoformat(rec["dateTime"].replace("Z", "+00:00"))
    ts_local = ts.astimezone()
    name = data.get("siteName", f"site {args.site}")

    if args.json:
        print(json.dumps({
            "site": name,
            "siteNumber": data.get("siteNumber"),
            "level_ft": level,
            "unit": data.get("value1Type", "Head"),
            "observed_utc": rec["dateTime"],
            "operating_range_max_ft": data.get("lakeOperatingRangeMax"),
        }, indent=2))
    else:
        age_min = (datetime.now(timezone.utc) - ts).total_seconds() / 60
        print(f"{name}")
        print(f"  Most recent lake level: {level:.2f} ft (MSL)")
        print(f"  Observed: {ts_local:%Y-%m-%d %I:%M %p %Z} ({age_min:.0f} min ago)")
        max_ft = data.get("lakeOperatingRangeMax")
        if max_ft:
            print(f"  Full pool: {max_ft:.1f} ft  ({max_ft - level:+.2f} ft from full)")

    if args.threshold is not None and level >= args.threshold:
        try:
            notify(args.ntfy_topic, level, name, rec["dateTime"])
            print(f"  ALERT: level >= {args.threshold} ft -> notified ntfy.sh/{args.ntfy_topic}",
                  file=sys.stderr)
        except Exception as e:
            print(f"Error posting ntfy alert: {e}", file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
