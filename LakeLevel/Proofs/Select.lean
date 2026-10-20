import LakeLevel.Spec.Response
import LakeLevel.Impl.Select

/-! # Obligations: selecting the most recent reading (R20–R22) -/

namespace LakeLevel

/-- `Latest` is functional: the spec picks at most one reading. -/
theorem Latest.unique {rs : List Reading} {r r' : Reading}
    (h : Latest rs r) (h' : Latest rs r') : r = r' := sorry

/-- `select` returns exactly the reading the spec describes. -/
theorem select_iff (rs : List Reading) (r : Reading) :
    select rs = some r ↔ Latest rs r := sorry

/-- … and only fails on an empty list. -/
theorem select_none_iff (rs : List Reading) : select rs = none ↔ rs = [] := sorry

end LakeLevel
