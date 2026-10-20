# PRD: `lake-level`, an LCRA lake level reporter and alerter

| | |
|---|---|
| **Status** | Draft for implementation |
| **Stage** | 0: English prose, the starting point of the formalization |

## 1. Background

The Lower Colorado River Authority (LCRA) operates the dams on the Highland
Lakes in Central Texas and publishes near-real-time telemetry from each dam
through its Hydromet site (`hydromet.lcra.org`). The charts on that site are
populated by a public JSON API, which we can call directly.

For a given **site** (e.g. site `3963`, Mansfield Dam, which impounds Lake
Travis) the API returns a site description plus a list of recent
**readings**, roughly one every five minutes going back about two weeks. Each
reading has a timestamp and the "head" elevation, which is the lake surface
level in feet above mean sea level (ft MSL).

People who live on or use the lake want to know the current level at a
glance, and want to be told when the lake rises to a level they care about
(flood watch, dock clearance, etc.).

## 2. Goals

1. Let a user see the current lake level for a site from the command line in
   under a few seconds.
2. Let a user (or a cron job) get a push notification on their phone when the
   lake level reaches a threshold they choose.
3. Provide a machine-readable output mode so the tool can feed other scripts.

### Non-goals

- Historical charts, trends, or forecasts.
- Storing readings anywhere.
- Deduplicating alerts across runs. (The tool is stateless; if it is run from
  cron every 15 minutes while the lake is high, it alerts every 15 minutes.
  That is acceptable for v1.)
- Any GUI or web UI.

## 3. Users & usage

- **Interactive user**: runs `lake-level` in a terminal and reads the result.
- **Automation**: runs `lake-level --threshold 685 --ntfy-topic my-lake` from
  cron, and relies on the exit status to detect failures.

## 4. Data source

```
GET https://hydromet.lcra.org/api/GetDataBySite/{site}/{type}
```

- `{site}` is the LCRA site number (default `3963`).
- `{type}` is the data type (default `lakelevel`).
- Send a `User-Agent` of `lake-level/1.0`.
- Give up after 30 seconds.

Example response (abridged):

```json
{
  "siteId": 55,
  "siteNumber": 3963,
  "siteName": "Mansfield Dam (Lake Travis)",
  "lakeOperatingRangeMax": 681.0,
  "value1Type": "Head",
  "value2Type": "Tail",
  "records": [
    {"dateTime": "2026-10-20T03:55:09Z", "value1": 677.58, "value2": 492.51},
    {"dateTime": "2026-10-20T03:50:02Z", "value1": 677.58, "value2": 492.57}
  ]
}
```

- `value1` is the lake level (because `value1Type` is `"Head"`). `value2` is
  the tailwater level below the dam and is not used.
- `lakeOperatingRangeMax` is the top of the conservation pool ("full pool").
  Not every site provides it.
- Records generally come newest-first, but we should not rely on that.

## 5. Functional requirements

### 5.1 Fetch and select

The tool fetches the data for the requested site and picks the most recent
reading.

### 5.2 Human-readable output (default)

Print the site name, the most recent lake level to two decimal places, when
it was observed (in the user's local time) and how long ago that was, and,
if the site reports a full-pool level, how far the lake is from full.

Example:

```
Mansfield Dam (Lake Travis)
  Most recent lake level: 677.58 ft (MSL)
  Observed: 2026-10-19 10:55 PM CDT (5 min ago)
  Full pool: 681.0 ft  (+3.42 ft from full)
```

The "from full" figure is full pool minus current level, so a positive number
means the lake is below full.

### 5.3 JSON output (`--json`)

Instead of the human-readable text, print a JSON object with the site name,
site number, the level, the unit, the observation time in UTC, and the
full-pool level (or null).

```json
{
  "site": "Mansfield Dam (Lake Travis)",
  "siteNumber": 3963,
  "level_ft": 677.58,
  "unit": "Head",
  "observed_utc": "2026-10-20T03:55:09Z",
  "operating_range_max_ft": 681.0
}
```

### 5.4 Threshold alerts (`--threshold FT`)

If a threshold is given and the lake level is at or above it, send a push
notification through [ntfy.sh](https://ntfy.sh) by POSTing to
`https://ntfy.sh/{topic}`:

- **Body**: `{site name} lake level is {level} ft (MSL) as of {observation
  time}.` followed by a second line, `Level has reached the alert threshold.`
- **Headers**: `Title: Lake level alert: {level} ft`, `Priority: high`,
  `Tags: warning,ocean`.

The topic is set with `--ntfy-topic` and defaults to `csarbora`. After a
successful notification, print a short note to stderr saying an alert was
sent and where.

Alerts work the same way in both output modes.

### 5.5 Command line

```
lake-level [--site N] [--type T] [--json] [--threshold FT] [--ntfy-topic TOPIC]
```

| Option | Default | Meaning |
|---|---|---|
| `--site` | `3963` | LCRA site number |
| `--type` | `lakelevel` | API data type |
| `--json` | off | Emit JSON instead of text |
| `--threshold` | none | Alert when level ≥ this many feet |
| `--ntfy-topic` | `csarbora` | ntfy.sh topic for alerts |

### 5.6 Errors

If anything goes wrong (network failure, a bad response, no readings), print
a one-line error message starting with `Error:` to stderr and exit with a
non-zero status. If the notification fails to send, that is also an error.
On success, exit 0.

## 6. Non-functional requirements

- Single executable, no runtime dependencies beyond what's on a normal Linux
  box.
- Runs in well under 5 seconds on a normal connection.
- Must be reliable enough to trust for flood alerting: it should never report
  a wrong level, and should never silently fail to alert.

## 7. Acceptance criteria

1. `lake-level` prints the current Lake Travis level, and it matches what the
   Hydromet website shows.
2. `lake-level --json | jq .level_ft` prints a number.
3. With `--threshold` set below the current level, a notification arrives on
   a phone subscribed to the topic.
4. With `--threshold` set above the current level, no notification is sent.
5. With the network unplugged, the tool prints an error and exits non-zero.
