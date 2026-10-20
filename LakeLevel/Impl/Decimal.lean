import LakeLevel.Spec.Decimal

/-! # Impl: exact decimal arithmetic, parsing, rounding, rendering -/

namespace LakeLevel

/-- Exact comparison `a ≤ b`, by cross-multiplying: `a.m·10^b.e ≤ b.m·10^a.e`. -/
def Dec.le (a b : Dec) : Bool :=
  decide (a.m * ((10 ^ b.e : Nat) : Int) ≤ b.m * ((10 ^ a.e : Nat) : Int))

/-- Exact difference over the common denominator `10^(a.e + b.e)`. -/
def Dec.sub (a b : Dec) : Dec :=
  ⟨a.m * ((10 ^ b.e : Nat) : Int) - b.m * ((10 ^ a.e : Nat) : Int), a.e + b.e⟩

/-- Left fold: `acc` is the value of the digits seen so far. -/
def digitsAcc : List Char → Nat → Nat
  | [], acc => acc
  | c :: cs, acc => digitsAcc cs (10 * acc + (c.toNat - 48))

def sgn (neg : Bool) : Int := if neg then -1 else 1

/-- Parse `-?[0-9]+(\.[0-9]+)?` exactly. -/
def parseDec (s : String) : Option Dec :=
  let (neg, rest) := match s.toList with
    | '-' :: r => (true, r)
    | r => (false, r)
  let a := rest.takeWhile Char.isDigit
  if a.isEmpty then none else
  match rest.dropWhile Char.isDigit with
  | [] => some ⟨sgn neg * (digitsAcc a 0 : Int), 0⟩
  | '.' :: b =>
    if !b.isEmpty && b.all Char.isDigit then
      some ⟨sgn neg * (digitsAcc (a ++ b) 0 : Int), b.length⟩
    else none
  | _ => none

/-- Round `N / D` to an integer, ties away from zero: for `N ≥ 0`,
`⌊(N + D/2) / D⌋ = ⌊(2N + D) / 2D⌋`; mirrored for `N < 0`. -/
def roundFrac (N : Int) (D : Nat) : Int :=
  if 0 ≤ N then (2 * N + D) / (2 * D)
  else -((2 * (-N) + D) / (2 * D))

/-- Round `d` to `n` places: the rounding of `d.m·10ⁿ / 10^d.e`. -/
def Dec.round (n : Nat) (d : Dec) : Int :=
  roundFrac (d.m * ((10 ^ n : Nat) : Int)) (10 ^ d.e)

/-- Decimal digits of `n`, most significant first, no leading zeros. -/
def natDigits (n : Nat) : List Char :=
  if n < 10 then [digitChar n] else natDigits (n / 10) ++ [digitChar (n % 10)]

/-- Render `k / 10ⁿ` with exactly `n` fractional digits (no `.` when `n = 0`). -/
def fixed (n : Nat) (k : Int) : String :=
  let a := k.natAbs
  let frac := natDigits (a % 10 ^ n)
  let fracPadded := List.replicate (n - frac.length) '0' ++ frac
  String.ofList <|
    (if k < 0 then ['-'] else []) ++ natDigits (a / 10 ^ n) ++
    (if n = 0 then [] else '.' :: fracPadded)

/-- `fixed`, with an explicit `+` for non-negative values. -/
def signed (n : Nat) (k : Int) : String :=
  if 0 ≤ k then "+" ++ fixed n k else fixed n k

end LakeLevel
