"""Run the original lake_level.py (test/original/) against a fixture, with
both network calls stubbed: fetch() returns the fixture, notify() records
instead of POSTing.
usage: python3 test/run_original.py FIXTURE.json [args...]"""
import importlib.util, json, pathlib, sys

sys.dont_write_bytecode = True  # leave no __pycache__ in test/original/
original = pathlib.Path(__file__).parent / "original" / "lake_level.py"
spec = importlib.util.spec_from_file_location("ll", original)
ll = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ll)
fixture = json.load(open(sys.argv[1]))
ll.fetch = lambda site, site_type: fixture
def notify(topic, level, name, observed):
    print(f"[stub notify: topic={topic} level={level}]", file=sys.stderr)
    return 200
ll.notify = notify
sys.argv = ["lake_level.py"] + sys.argv[2:]
sys.exit(ll.main())
