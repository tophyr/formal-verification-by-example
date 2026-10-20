"""Check the HTML lessons in docs/ against the repository.

* Every code excerpt marked <code data-src="REF:PATH:A-B"> must be exactly
  lines A..B of PATH at git ref REF. Excerpts can't drift from the source.
* Every <a data-gh="..."> must name a ref, path and line range that exist.
  A commit link must be in the published history (an ancestor of HEAD), its
  text must name the same commit, and inside a page's stage-links box it must
  be the commit that box's stage tag points at. So a rewritten history can't
  leave links to commits that only survive locally.
* Every relative href must point at a file that exists.

Run from the repository root:  python3 -I scripts/check-lessons.py
Exits non-zero, listing every problem, if anything is wrong.
"""
import html.parser
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
DOCS = ROOT / "docs"


def git(*args):
    r = subprocess.run(["git", "-C", str(ROOT), *args], capture_output=True, text=True)
    return r.returncode, r.stdout, r.stderr


_blobs = {}


def blob(ref, path):
    """File contents at ref, or None if it doesn't exist there. The ref `main`
    means the working tree: the pages are published from main, so a link to
    main must be right for what is about to be committed."""
    key = (ref, path)
    if key not in _blobs:
        if ref == "main":
            f = ROOT / path
            _blobs[key] = f.read_text() if f.is_file() else None
        else:
            rc, out, _ = git("show", f"{ref}:{path}")
            _blobs[key] = out if rc == 0 else None
    return _blobs[key]


def ref_exists(ref):
    return git("rev-parse", "--verify", "--quiet", f"{ref}^{{commit}}")[0] == 0


class Page(html.parser.HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.excerpts = []  # (data-src, text, line)
        self.gh = []        # (data-gh, line)
        self.hrefs = []     # (href, line)
        self.commits = []   # (sha, link text, stage-links box's <strong> text or None, line)
        self._cur = None
        self._depth = 0     # <div> nesting depth
        self._box = None    # depth of the open stage-links <div>, if any
        self._strong = None # text of the stage-links box's <strong>
        self._text = None   # [kind, chunks] while collecting a <strong> or commit link's text

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        line = self.getpos()[0]
        if tag == "code" and "data-src" in a:
            if self._cur is not None:
                raise ValueError(f"line {line}: nested data-src")
            self._cur = [a["data-src"], [], line]
        elif self._cur is not None:
            raise ValueError(f"line {line}: <{tag}> inside a data-src excerpt")
        if tag == "div":
            self._depth += 1
            if "stage-links" in a.get("class", "").split():
                self._box, self._strong = self._depth, None
        if tag == "strong" and self._box is not None:
            self._text = ["strong", []]
        if tag == "a":
            if "data-gh" in a:
                self.gh.append((a["data-gh"], line))
                if m := re.fullmatch(r"commit/([0-9a-f]{7,40})", a["data-gh"]):
                    self._text = ["commit", [], m[1], line]
            if a.get("href"):
                self.hrefs.append((a["href"], line))
        if tag in ("link", "script") and (a.get("href") or a.get("src")):
            self.hrefs.append((a.get("href") or a.get("src"), line))

    def handle_endtag(self, tag):
        if tag == "code" and self._cur is not None:
            self.excerpts.append((self._cur[0], "".join(self._cur[1]), self._cur[2]))
            self._cur = None
        if tag == "strong" and self._text and self._text[0] == "strong":
            self._strong, self._text = "".join(self._text[1]).strip(), None
        if tag == "a" and self._text and self._text[0] == "commit":
            box = self._strong if self._box is not None else None
            self.commits.append((self._text[2], "".join(self._text[1]).strip(), box, self._text[3]))
            self._text = None
        if tag == "div":
            if self._box == self._depth:
                self._box = None
            self._depth -= 1

    def handle_data(self, data):
        if self._cur is not None:
            self._cur[1].append(data)
        if self._text is not None:
            self._text[1].append(data)


def check_excerpt(spec, text):
    m = re.fullmatch(r"([^:]+):([^:]+):(\d+)-(\d+)", spec)
    if not m:
        return f"bad data-src {spec!r}"
    ref, path, a, b = m[1], m[2], int(m[3]), int(m[4])
    src = blob(ref, path)
    if src is None:
        return f"{path} does not exist at {ref}"
    lines = src.split("\n")
    if not (1 <= a <= b <= len(lines)):
        return f"{spec}: lines out of range (file has {len(lines)})"
    want = "\n".join(lines[a - 1:b])
    got = text[1:] if text.startswith("\n") else text
    got = got[:-1] if got.endswith("\n") else got
    if got != want:
        for i, (w, g) in enumerate(zip(want.split("\n") + [""] * 99, got.split("\n") + [""] * 99)):
            if w != g:
                return f"{spec}: excerpt differs at line {a + i}:\n    source:  {w!r}\n    excerpt: {g!r}"
    return None


def check_gh(spec):
    if m := re.fullmatch(r"blob/([^/]+)/([^#]+)(?:#L(\d+)(?:-L(\d+))?)?", spec):
        ref, path = m[1], m[2]
        src = blob(ref, path)
        if src is None:
            return f"{path} does not exist at {ref}"
        n = len(src.split("\n"))
        for x in (m[3], m[4]):
            if x and not 1 <= int(x) <= n:
                return f"{spec}: line {x} out of range (file has {n})"
        return None
    if m := re.fullmatch(r"tree/([^/]+)(?:/(.+))?", spec):
        if not ref_exists(m[1]):
            return f"no ref {m[1]}"
        if m[2]:
            there = (ROOT / m[2]).exists() if m[1] == "main" else \
                git("cat-file", "-e", f"{m[1]}:{m[2]}")[0] == 0
            if not there:
                return f"{m[2]} does not exist at {m[1]}"
        return None
    if m := re.fullmatch(r"compare/(.+)\.\.\.(.+)", spec):
        bad = [r for r in (m[1], m[2]) if not ref_exists(r)]
        return f"no ref {bad}" if bad else None
    if m := re.fullmatch(r"commit/([0-9a-f]{7,40})", spec):
        return None if ref_exists(m[1]) else f"no commit {m[1]}"
    return f"unrecognized data-gh {spec!r}"


def check_commit(sha, text, box):
    if not ref_exists(sha):
        return None  # already reported by check_gh
    if git("merge-base", "--is-ancestor", sha, "HEAD")[0] != 0:
        return f"commit {sha} is not in the published history (not an ancestor of HEAD)"
    words = text.split()
    if not words or not re.fullmatch(r"[0-9a-f]{7,40}", words[-1]) \
            or git("rev-parse", words[-1])[1] != git("rev-parse", sha)[1]:
        return f"commit link to {sha} is labelled {text!r}"
    if box is not None:
        m = re.fullmatch(r"Stage (\d+)", box)
        if not m:
            return f"stage-links box titled {box!r}, expected 'Stage N'"
        tag = f"stage-{m[1]}"
        if git("rev-parse", f"{tag}^{{commit}}")[1] != git("rev-parse", sha)[1]:
            return f"{box} box links commit {sha}, but {tag} is {git('rev-parse', '--short', tag)[1].strip()}"
    return None


def main():
    problems, n_ex, n_gh, n_href = [], 0, 0, 0
    pages = sorted(DOCS.rglob("*.html"))
    for page in pages:
        rel = page.relative_to(ROOT)
        p = Page()
        try:
            p.feed(page.read_text())
        except ValueError as e:
            problems.append(f"{rel}: {e}")
            continue
        for spec, text, line in p.excerpts:
            n_ex += 1
            if err := check_excerpt(spec, text):
                problems.append(f"{rel}:{line}: {err}")
        for spec, line in p.gh:
            n_gh += 1
            if err := check_gh(spec):
                problems.append(f"{rel}:{line}: {err}")
        for sha, text, box, line in p.commits:
            if err := check_commit(sha, text, box):
                problems.append(f"{rel}:{line}: {err}")
        for href, line in p.hrefs:
            if re.match(r"[a-z]+:", href) or href.startswith("#"):
                continue
            n_href += 1
            target = (page.parent / href.split("#")[0]).resolve()
            if not target.exists():
                problems.append(f"{rel}:{line}: broken link {href}")
    print(f"{len(pages)} pages: {n_ex} excerpts, {n_gh} repository links, {n_href} local links checked")
    if problems:
        print("\n".join(problems))
        print(f"{len(problems)} problem(s)")
        sys.exit(1)
    print("all match the repository")


main()
