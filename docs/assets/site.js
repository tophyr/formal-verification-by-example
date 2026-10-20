// formal-verification-by-example lessons: repository links, excerpt captions,
// Lean syntax highlighting, and the light/dark toggle. No dependencies.

// If you serve these pages from a custom domain, set this to the repository
// URL, e.g. "https://github.com/you/formal-verification-by-example". On a normal
// GitHub Pages URL (https://OWNER.github.io/REPO/...) it is worked out
// automatically.
const CONFIG_REPO = "";

function repoURL() {
  if (CONFIG_REPO) return CONFIG_REPO.replace(/\/$/, "");
  const host = location.hostname;
  if (!host.endsWith(".github.io")) return null;
  const owner = host.slice(0, -".github.io".length);
  const repo = location.pathname.split("/").filter(Boolean)[0];
  return repo ? `https://github.com/${owner}/${repo}` : null;
}

// The git command that shows the same thing locally.
function gitCommand(spec) {
  let m;
  if ((m = spec.match(/^blob\/([^/]+)\/([^#]+)/))) return `git show ${m[1]}:${m[2]}`;
  if ((m = spec.match(/^tree\/([^/]+)/))) return `git checkout ${m[1]}`;
  if ((m = spec.match(/^compare\/(.+)\.\.\.(.+)$/))) return `git diff ${m[1]} ${m[2]}`;
  if ((m = spec.match(/^commit\/(.+)$/))) return `git show ${m[1]}`;
  return spec;
}

function wireLinks(repo) {
  for (const a of document.querySelectorAll("a[data-gh]")) {
    const spec = a.dataset.gh;
    a.title = gitCommand(spec);
    if (repo) {
      a.href = `${repo}/${spec}`;
      a.classList.add("gh");
    } else if (!a.getAttribute("href")) {
      // Viewed locally with no repository URL: show the git command instead.
      const code = document.createElement("code");
      code.className = "gitcmd";
      code.textContent = gitCommand(spec);
      a.replaceWith(code);
    }
  }
}

// <code data-src="stage-6:LakeLevel/Impl/Select.lean:7-11"> gets a caption
// linking to those lines. scripts/check-lessons.py verifies the text matches.
function captionExcerpts(repo) {
  for (const code of document.querySelectorAll("code[data-src]")) {
    const [ref, path, range] = code.dataset.src.split(":");
    const [a, b] = range.split("-");
    const pre = code.parentElement;
    const fig = document.createElement("figure");
    fig.className = "excerpt";
    const cap = document.createElement("figcaption");
    const left = document.createElement("span");
    const link = document.createElement("a");
    const anchor = b && b !== a ? `#L${a}-L${b}` : `#L${a}`;
    link.dataset.gh = `blob/${ref}/${path}${anchor}`;
    link.textContent = path;
    left.append(link, ` · line${b && b !== a ? "s" : ""} ${a}${b && b !== a ? "–" + b : ""}`);
    const right = document.createElement("span");
    right.textContent = `as of ${ref}`;
    cap.append(left, right);
    pre.replaceWith(fig);
    fig.append(cap, pre);
  }
}

const KEYWORDS = new Set(("def theorem structure inductive abbrev instance where namespace end open " +
  "import private section variable match with fun if then else let do return deriving by have show " +
  "from at partial for in unless try catch mut elab").split(" "));
const TACTICS = new Set(("unfold rw simp simp_all simpa omega decide exact refine intro rintro obtain " +
  "cases rcases induction constructor apply subst split by_cases left right exact_mod_cast generalize " +
  "dsimp infer_instance trace_state first revert rfl").split(" "));

function esc(s) {
  return s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}

function highlightLean(src) {
  const re = /(\/-[\s\S]*?-\/)|(--[^\n]*)|("(?:\\.|[^"\\])*")|('(?:\\.|[^\\'\n])')|(\b\d+\b)|([A-Za-z_][A-Za-z0-9_'!?.]*)/g;
  let out = "", last = 0, m;
  while ((m = re.exec(src))) {
    out += esc(src.slice(last, m.index));
    const t = m[0];
    if (m[1] || m[2]) out += `<span class="tok-com">${esc(t)}</span>`;
    else if (m[3] || m[4]) out += `<span class="tok-str">${esc(t)}</span>`;
    else if (m[5]) out += `<span class="tok-num">${t}</span>`;
    else if (t === "sorry" || t === "admit" || t === "native_decide") out += `<span class="tok-sorry">${t}</span>`;
    else if (KEYWORDS.has(t)) out += `<span class="tok-kw">${t}</span>`;
    else if (TACTICS.has(t)) out += `<span class="tok-tac">${t}</span>`;
    else out += esc(t);
    last = re.lastIndex;
  }
  return out + esc(src.slice(last));
}

// Goal-state output: hypothesis names and the ⊢ line stand out.
function highlightGoal(src) {
  return src.split("\n").map((line) => {
    if (line.startsWith("⊢")) return `<span class="tok-goal">${esc(line)}</span>`;
    const m = line.match(/^([^\s:][^:]*?) : (.*)$/);
    if (m && !line.startsWith(" ")) return `<span class="tok-hyp">${esc(m[1])}</span> : ${esc(m[2])}`;
    return esc(line);
  }).join("\n");
}

function highlight() {
  for (const el of document.querySelectorAll("code.lean")) el.innerHTML = highlightLean(el.textContent);
  for (const el of document.querySelectorAll("code.goal")) el.innerHTML = highlightGoal(el.textContent);
}

function themeToggle() {
  const btn = document.querySelector(".theme-toggle");
  if (!btn) return;
  const root = document.documentElement;
  const get = () => {
    try { return localStorage.getItem("theme"); } catch { return null; }
  };
  const set = (v) => {
    try { localStorage.setItem("theme", v); } catch { /* storage unavailable */ }
  };
  const saved = get();
  if (saved === "light" || saved === "dark") root.dataset.theme = saved;
  const current = () => root.dataset.theme ||
    (matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light");
  const label = () => { btn.textContent = current() === "dark" ? "Light" : "Dark"; };
  label();
  btn.addEventListener("click", () => {
    root.dataset.theme = current() === "dark" ? "light" : "dark";
    set(root.dataset.theme);
    label();
  });
}

document.addEventListener("DOMContentLoaded", () => {
  const repo = repoURL();
  highlight();
  captionExcerpts(repo);
  wireLinks(repo);
  themeToggle();
});
