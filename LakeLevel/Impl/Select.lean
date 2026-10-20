import LakeLevel.Types

/-! # Impl: choose the most recent reading -/

namespace LakeLevel

/-- Keep the first reading seen with the latest instant: replace only on *strictly* later. -/
def select (rs : List Reading) : Option Reading :=
  match rs with
  | [] => none
  | r :: rest => some (rest.foldl (fun best x => if best.t < x.t then x else best) r)

end LakeLevel
