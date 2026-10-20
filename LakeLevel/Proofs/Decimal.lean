import LakeLevel.Spec.Decimal
import LakeLevel.Impl.Decimal

/-! # Obligations: decimals (R16, R31, R32, R50 comparison, A4, A6) -/

namespace LakeLevel

/-- The rounding spec is *deterministic*: at most one correct answer.
(A spec with two acceptable answers would let two "verified" programs disagree.) -/
theorem RoundsTo.unique {x : Rat} {k k' : Int} (h : RoundsTo x k) (h' : RoundsTo x k') :
    k = k' := sorry

/-- Comparison is exactly rational `≤`. -/
theorem Dec.le_iff (a b : Dec) : Dec.le a b = true ↔ a.val ≤ b.val := sorry

/-- Subtraction is exact. -/
theorem Dec.sub_val (a b : Dec) : (Dec.sub a b).val = a.val - b.val := sorry

/-- The parser accepts exactly `DecLit`, and returns what the literal denotes. -/
theorem parseDec_iff (s : String) (d : Dec) :
    parseDec s = some d ↔ ∃ neg a b, DecLit s neg a b ∧ d = DecLit.den neg a b := sorry

/-- `roundFrac` meets the rounding spec. -/
theorem roundFrac_spec (N : Int) (D : Nat) (hD : 0 < D) :
    RoundsTo ((N : Rat) / (D : Rat)) (roundFrac N D) := sorry

/-- Rounding to `n` places meets the rounding spec on `d · 10ⁿ`. -/
theorem Dec.round_spec (n : Nat) (d : Dec) :
    RoundsTo (d.val * ((10 ^ n : Nat) : Rat)) (Dec.round n d) := sorry

/-- Rendered text has the promised shape … -/
theorem fixed_shape (n : Nat) (k : Int) (hn : 1 ≤ n) : FixedShape n (fixed n k) := sorry

/-- … starts with `-` exactly when the value is negative … -/
theorem fixed_neg (n : Nat) (k : Int) (hn : 1 ≤ n) :
    (fixed n k).toList.head? = some '-' ↔ k < 0 := sorry

/-- … and reads back as exactly `k / 10ⁿ`. -/
theorem parseDec_fixed (n : Nat) (k : Int) (hn : 1 ≤ n) :
    parseDec (fixed n k) = some ⟨k, n⟩ := sorry

/-- Signed rendering (R32): `+` iff non-negative, never `-0.00`. -/
theorem signed_eq (n : Nat) (k : Int) :
    signed n k = if 0 ≤ k then "+" ++ fixed n k else fixed n k := sorry

end LakeLevel
