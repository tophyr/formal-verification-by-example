import LakeLevel.Types

/-! # Impl: exact decimal arithmetic, parsing, rounding, rendering -/

namespace LakeLevel

/-- Exact comparison `a ≤ b`. -/
def Dec.le (a b : Dec) : Bool := sorry

/-- Exact difference `a - b`. -/
def Dec.sub (a b : Dec) : Dec := sorry

/-- Parse `-?[0-9]+(\.[0-9]+)?` exactly. -/
def parseDec (s : String) : Option Dec := sorry

/-- Round the fraction `N / D` to an integer, ties away from zero. -/
def roundFrac (N : Int) (D : Nat) : Int := sorry

/-- Round `d` to `n` decimal places, as a count of `10⁻ⁿ` units. -/
def Dec.round (n : Nat) (d : Dec) : Int := sorry

/-- Render `k / 10ⁿ` with exactly `n` fractional digits. -/
def fixed (n : Nat) (k : Int) : String := sorry

/-- `fixed`, with an explicit `+` for non-negative values. -/
def signed (n : Nat) (k : Int) : String := sorry

end LakeLevel
