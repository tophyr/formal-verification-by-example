import LakeLevel.Types

/-!
# Spec: exact decimals, rounding, decimal syntax

docs/02-formal-model.md §2.1. Everything here says *what* a correct answer is;
nothing here is an algorithm the implementation could copy.
-/

namespace LakeLevel

/-- The rational number a `Dec` denotes: `m / 10^e`. All semantics go through this. -/
def Dec.val (d : Dec) : Rat := (d.m : Rat) / ((10 ^ d.e : Nat) : Rat)

/-- **Rounding, relationally** (A4). `k` is a correct rounding of `x`, ties
away from zero:

* `x` is strictly within ½ of `k`, or
* `x` is exactly ½ below `k` and positive (so `k` is farther from zero), or
* `x` is exactly ½ above `k` and negative (likewise).

No algorithm is given. Stage 5 proves exactly one `k` satisfies this. -/
def RoundsTo (x : Rat) (k : Int) : Prop :=
  ((k : Rat) - 1/2 < x ∧ x < (k : Rat) + 1/2) ∨
  (x = (k : Rat) - 1/2 ∧ 0 < x) ∨
  (x = (k : Rat) + 1/2 ∧ x < 0)

/-- The value of a decimal digit character. -/
def digitVal (c : Char) : Nat := c.toNat - '0'.toNat

/-- The character for a digit `0 ≤ n ≤ 9`. -/
def digitChar (n : Nat) : Char := Char.ofNat ('0'.toNat + n)

/-- **Positional notation**, written right-recursively with powers of ten:
`d₀ d₁ … dₙ₋₁ = d₀·10ⁿ⁻¹ + (d₁ … dₙ₋₁)`. (The implementation uses a
left fold with an accumulator; Stage 5 proves they agree.) -/
def digitsVal : List Char → Nat
  | [] => 0
  | c :: cs => digitVal c * 10 ^ cs.length + digitsVal cs

/-- `s` is the decimal literal `-?[0-9]+(\.[0-9]+)?` with sign `neg`,
integer digits `a` and fraction digits `b` (A6). -/
def DecLit (s : String) (neg : Bool) (a b : List Char) : Prop :=
  a ≠ [] ∧ (∀ c ∈ a, c.isDigit) ∧ (∀ c ∈ b, c.isDigit) ∧
  s.toList = (if neg then ['-'] else []) ++ a ++ (if b = [] then [] else '.' :: b)

/-- The exact decimal a literal with these parts denotes. -/
def DecLit.den (neg : Bool) (a b : List Char) : Dec :=
  ⟨(if neg then -1 else 1) * (digitsVal (a ++ b) : Int), b.length⟩

/-- The text shape `fixed n k` must have: `-?(0|[1-9][0-9]*)\.[0-9]{n}`,
or `-?(0|[1-9][0-9]*)` when `n = 0`. -/
def FixedShape (n : Nat) (s : String) : Prop :=
  ∃ (neg : Bool) (a b : List Char),
    DecLit s neg a b ∧ b.length = n ∧ (a = ['0'] ∨ a.head? ≠ some '0')

end LakeLevel
