import LakeLevel.Spec.Prog
import LakeLevel.Impl.Args
import LakeLevel.Impl.Decode
import LakeLevel.Impl.Render

/-! # Impl: the whole program, as a `Prog` value -/

namespace LakeLevel

/-- After the report is written: alert if required (R50–R54). -/
def finish (cfg : Cfg) (S : Site) (R : Reading) : Prog :=
  match cfg.threshold with
  | some th =>
    if Dec.le th.value R.level then
      .post (alertReq cfg S R) fun
        | .response st =>
          if ok2xx st then .err (alertNotice cfg) (.done 0)
          else .err (errLine (sanitize s!"ntfy alert failed: HTTP {st}")) (.done 1)
        | .failed m => .err (errLine (sanitize s!"ntfy alert failed: {m}")) (.done 1)
    else .done 0
  | none => .done 0

def main (argv : List String) : Prog :=
  match parseArgs argv with
  | .help => .out helpText (.done 0)
  | .usage m => .err (errLine (sanitize m) ++ usageText) (.done 2)
  | .ok cfg =>
    .get (fetchReq cfg) fun
      | .failed m => .err (errLine (sanitize m)) (.done 1)
      | .response st body =>
        if ok2xx st then
          match decodeBody (siteNum cfg.site) body with
          | .error m => .err (errLine (sanitize m)) (.done 1)
          | .ok (S, R) =>
            if cfg.json then .out (jsonText S R) (finish cfg S R)
            else
              .zoneAt R.t fun z => .clock fun now =>
                .out (humanReport S R z now) (finish cfg S R)
        else .err (errLine (sanitize s!"hydromet returned HTTP {st}")) (.done 1)

end LakeLevel
