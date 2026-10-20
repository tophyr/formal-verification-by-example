import LakeLevel.Spec.Args
import LakeLevel.Impl.Decimal

/-! # Impl: command-line parsing and the fetch request -/

namespace LakeLevel

def parseArgs (argv : List String) : ArgResult := sorry

/-- The numeric value of a validated site string. -/
def siteNum (s : String) : Nat := sorry

/-- The GET request for a configuration (R4). -/
def fetchReq (cfg : Cfg) : Request := sorry

end LakeLevel
