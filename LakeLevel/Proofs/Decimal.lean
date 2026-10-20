import LakeLevel.Spec.Decimal
import LakeLevel.Impl.Decimal
import LakeLevel.Proofs.DecimalLemmas

/-! # Obligations: decimals (R16, R31, R32, R50 comparison, A4, A6) -/

namespace LakeLevel

/-- The rounding spec is *deterministic*: at most one correct answer.
(A spec with two acceptable answers would let two "verified" programs disagree.) -/
theorem RoundsTo.unique {x : Rat} {k k' : Int} (h : RoundsTo x k) (h' : RoundsTo x k') :
    k = k' := RoundsTo.unique' h h'

/-- Comparison is exactly rational `≤`. -/
theorem Dec.le_iff (a b : Dec) : Dec.le a b = true ↔ a.val ≤ b.val := Dec.le_iff' a b

/-- Subtraction is exact. -/
theorem Dec.sub_val (a b : Dec) : (Dec.sub a b).val = a.val - b.val := Dec.sub_val' a b

/-- The parser accepts exactly `DecLit`, and returns what the literal denotes. -/
theorem parseDec_iff (s : String) (d : Dec) :
    parseDec s = some d ↔ ∃ neg a b, DecLit s neg a b ∧ d = DecLit.den neg a b := parseDec_iff' s d

/-- `roundFrac` meets the rounding spec. -/
theorem roundFrac_spec (N : Int) (D : Nat) (hD : 0 < D) :
    RoundsTo ((N : Rat) / (D : Rat)) (roundFrac N D) := roundFrac_spec' N D hD

/-- Rounding to `n` places meets the rounding spec on `d · 10ⁿ`. -/
theorem Dec.round_spec (n : Nat) (d : Dec) :
    RoundsTo (d.val * ((10 ^ n : Nat) : Rat)) (Dec.round n d) := Dec.round_spec' n d

/-- Rendered text has the promised shape … -/
theorem fixed_shape (n : Nat) (k : Int) : FixedShape n (fixed n k) := fixed_shape' n k

/-- … starts with `-` exactly when the value is negative … -/
theorem fixed_neg (n : Nat) (k : Int) :
    (fixed n k).toList.head? = some '-' ↔ k < 0 := fixed_neg' n k

/-- … and reads back as exactly `k / 10ⁿ`. -/
theorem parseDec_fixed (n : Nat) (k : Int) :
    parseDec (fixed n k) = some ⟨k, n⟩ := parseDec_fixed' n k

/-- Signed rendering (R32): `+` iff non-negative, never `-0.00`. -/
theorem signed_eq (n : Nat) (k : Int) :
    signed n k = if 0 ≤ k then "+" ++ fixed n k else fixed n k := rfl

end LakeLevel
