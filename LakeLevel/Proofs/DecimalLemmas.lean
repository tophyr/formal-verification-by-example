import LakeLevel.Spec.Decimal
import LakeLevel.Impl.Decimal

/-! # Helper lemmas for `Proofs/Decimal.lean` -/

namespace LakeLevel

/-! ## Bridging `Rat` fractions to integer arithmetic -/

theorem frac_lt (N M : Int) (D E : Nat) (hD : 0 < D) (hE : 0 < E) :
    (N : Rat) / (D : Rat) < (M : Rat) / (E : Rat) ↔ N * E < M * D := by
  have hD' : (0 : Rat) < (D : Rat) := by exact_mod_cast hD
  have hE' : (0 : Rat) < (E : Rat) := by exact_mod_cast hE
  have : (M : Rat) / (E : Rat) * (D : Rat) = ((M * D : Int) : Rat) / (E : Rat) := by
    rw [Rat.intCast_mul, Rat.div_def, Rat.div_def]; simp only [Rat.intCast_natCast]
    rw [Rat.mul_assoc, Rat.mul_comm (E : Rat)⁻¹, ← Rat.mul_assoc]
  rw [Rat.div_lt_iff hD', this, Rat.lt_div_iff hE']
  have h2 : (N : Rat) * (E : Rat) = ((N * E : Int) : Rat) := by
    rw [Rat.intCast_mul]; simp only [Rat.intCast_natCast]
  rw [h2, Rat.intCast_lt_intCast]

theorem frac_le (N M : Int) (D E : Nat) (hD : 0 < D) (hE : 0 < E) :
    (N : Rat) / (D : Rat) ≤ (M : Rat) / (E : Rat) ↔ N * E ≤ M * D := by
  rw [← Rat.not_lt, frac_lt M N E D hE hD]; omega

theorem frac_eq (N M : Int) (D E : Nat) (hD : 0 < D) (hE : 0 < E) :
    (N : Rat) / (D : Rat) = (M : Rat) / (E : Rat) ↔ N * E = M * D := by
  constructor
  · intro h
    have h1 := (frac_le N M D E hD hE).1 (h ▸ Rat.le_refl)
    have h2 := (frac_le M N E D hE hD).1 (h ▸ Rat.le_refl)
    omega
  · intro h
    exact Rat.le_antisymm ((frac_le N M D E hD hE).2 (by omega)) ((frac_le M N E D hE hD).2 (by omega))

/-- An integer as a fraction over any positive denominator. -/
theorem int_as_frac (k : Int) (D : Nat) (hD : 0 < D) :
    (k : Rat) = ((k * D : Int) : Rat) / (D : Rat) := by
  have hD' : (D : Rat) ≠ 0 := by
    have : (0 : Rat) < (D : Rat) := by exact_mod_cast hD
    exact Rat.ne_of_gt this
  rw [Rat.intCast_mul, Rat.intCast_natCast, Rat.mul_div_cancel hD']

theorem pow10_pos (e : Nat) : 0 < 10 ^ e := Nat.pow_pos (by decide)


theorem half_below (k : Int) : (k : Rat) - 1/2 = ((2 * k - 1 : Int) : Rat) / ((2 : Nat) : Rat) := by
  simp only [Rat.intCast_sub, Rat.intCast_mul]
  grind

theorem half_above (k : Int) : (k : Rat) + 1/2 = ((2 * k + 1 : Int) : Rat) / ((2 : Nat) : Rat) := by
  simp only [Rat.intCast_add, Rat.intCast_mul]
  grind

theorem zero_frac : (0 : Rat) = ((0 : Int) : Rat) / ((1 : Nat) : Rat) := by
  rw [Rat.intCast_zero, Rat.div_def, Rat.zero_mul]

/-- `RoundsTo` for a fraction, in integer form. -/
theorem roundsTo_frac (N k : Int) (D : Nat) (hD : 0 < D) :
    RoundsTo ((N : Rat) / (D : Rat)) k ↔
      (((2 * k - 1) * D < N * 2 ∧ N * 2 < (2 * k + 1) * D) ∨
       (N * 2 = (2 * k - 1) * D ∧ 0 < N) ∨
       (N * 2 = (2 * k + 1) * D ∧ N < 0)) := by
  unfold RoundsTo
  rw [half_below, half_above, frac_lt _ _ 2 D (by decide) hD, frac_lt _ _ D 2 hD (by decide),
    frac_eq _ _ D 2 hD (by decide), frac_eq _ _ D 2 hD (by decide), zero_frac,
    frac_lt _ _ 1 D (by decide) hD, frac_lt _ _ D 1 hD (by decide)]
  have hD' : (0 : Int) < D := by omega
  constructor <;> intro h <;> omega

theorem RoundsTo.unique' {x : Rat} {k k' : Int} (h : RoundsTo x k) (h' : RoundsTo x k') :
    k = k' := by
  have a : ((k' - k : Int) : Rat) < ((1 : Int) : Rat) := by
    simp only [Rat.intCast_sub, Rat.intCast_one]
    unfold RoundsTo at h h'
    rcases h with h | h | h <;> rcases h' with h' | h' | h' <;> grind
  have b : ((k - k' : Int) : Rat) < ((1 : Int) : Rat) := by
    simp only [Rat.intCast_sub, Rat.intCast_one]
    unfold RoundsTo at h h'
    rcases h with h | h | h <;> rcases h' with h' | h' | h' <;> grind
  rw [Rat.intCast_lt_intCast] at a b
  omega

/-- Ties-away rounding of a non-negative fraction, in integer form. -/
theorem roundFrac_int (N : Int) (D : Nat) (hD : 0 < D) :
    let k := roundFrac N D
    ((2 * k - 1) * D < N * 2 ∧ N * 2 < (2 * k + 1) * D) ∨
    (N * 2 = (2 * k - 1) * D ∧ 0 < N) ∨
    (N * 2 = (2 * k + 1) * D ∧ N < 0) := by
  intro k
  have hD' : (0 : Int) < (D : Int) := by omega
  have h2D : (0 : Int) < 2 * (D : Int) := by omega
  by_cases hN : 0 ≤ N
  · have hk : k = (2 * N + D) / (2 * D) := by simp [k, roundFrac, hN]
    have lo := Int.ediv_mul_le (2 * N + D) (Int.ne_of_gt h2D)
    have hi := Int.lt_ediv_add_one_mul_self (2 * N + D) h2D
    rw [← hk] at lo hi
    have e1 : k * (2 * (D : Int)) = 2 * (k * D) := by rw [Int.mul_left_comm]
    have e2 : (k + 1) * (2 * (D : Int)) = 2 * (k * D) + 2 * D := by
      rw [Int.add_mul, e1, Int.one_mul]
    have e3 : (2 * k - 1) * (D : Int) = 2 * (k * D) - D := by
      rw [Int.sub_mul, Int.mul_assoc, Int.one_mul]
    have e4 : (2 * k + 1) * (D : Int) = 2 * (k * D) + D := by
      rw [Int.add_mul, Int.mul_assoc, Int.one_mul]
    rw [e1] at lo; rw [e2] at hi; rw [e3, e4]
    by_cases hz : N = 0
    · -- then k = D / 2D = 0
      have : k = 0 := by
        rw [hk, hz]; simp
        exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
      rw [this, Int.zero_mul]; omega
    · omega
  · have hk : k = -((2 * (-N) + D) / (2 * D)) := by simp [k, roundFrac, hN]
    generalize hq : (2 * (-N) + D) / (2 * D) = q at hk
    have lo := Int.ediv_mul_le (2 * (-N) + D) (Int.ne_of_gt h2D)
    have hi := Int.lt_ediv_add_one_mul_self (2 * (-N) + D) h2D
    rw [hq] at lo hi
    rw [hk]
    have e1 : q * (2 * (D : Int)) = 2 * (q * D) := by rw [Int.mul_left_comm]
    have e2 : (q + 1) * (2 * (D : Int)) = 2 * (q * D) + 2 * D := by
      rw [Int.add_mul, e1, Int.one_mul]
    have e3 : (2 * -q - 1) * (D : Int) = -(2 * (q * D)) - D := by
      rw [Int.sub_mul, Int.mul_assoc, Int.one_mul, Int.neg_mul, Int.mul_neg]
    have e4 : (2 * -q + 1) * (D : Int) = -(2 * (q * D)) + D := by
      rw [Int.add_mul, Int.mul_assoc, Int.one_mul, Int.neg_mul, Int.mul_neg]
    rw [e1] at lo; rw [e2] at hi; rw [e3, e4]
    omega

theorem roundFrac_spec' (N : Int) (D : Nat) (hD : 0 < D) :
    RoundsTo ((N : Rat) / (D : Rat)) (roundFrac N D) :=
  (roundsTo_frac N _ D hD).2 (roundFrac_int N D hD)

theorem Dec.le_iff' (a b : Dec) : Dec.le a b = true ↔ a.val ≤ b.val := by
  unfold Dec.le Dec.val
  rw [decide_eq_true_iff, frac_le _ _ _ _ (pow10_pos _) (pow10_pos _)]

theorem Dec.sub_val' (a b : Dec) : (Dec.sub a b).val = a.val - b.val := by
  unfold Dec.sub Dec.val
  have hA : ((10 ^ a.e : Nat) : Int) ≠ 0 := by have := pow10_pos a.e; omega
  have hB : ((10 ^ b.e : Nat) : Int) ≠ 0 := by have := pow10_pos b.e; omega
  have e : ((10 ^ (a.e + b.e) : Nat) : Rat) = (((10 ^ a.e : Nat) : Int) * ((10 ^ b.e : Nat) : Int) : Int) := by
    rw [Nat.pow_add, Rat.intCast_mul, Rat.intCast_natCast, Rat.intCast_natCast, Rat.natCast_mul]
  simp only
  rw [e, ← Rat.intCast_natCast (10 ^ a.e), ← Rat.intCast_natCast (10 ^ b.e),
    ← Rat.divInt_eq_div, ← Rat.divInt_eq_div, ← Rat.divInt_eq_div, Rat.divInt_sub_divInt _ _ hA hB]

theorem Dec.round_spec' (n : Nat) (d : Dec) :
    RoundsTo (d.val * ((10 ^ n : Nat) : Rat)) (Dec.round n d) := by
  unfold Dec.round Dec.val
  have : (d.m : Rat) / ((10 ^ d.e : Nat) : Rat) * ((10 ^ n : Nat) : Rat) =
      ((d.m * ((10 ^ n : Nat) : Int) : Int) : Rat) / ((10 ^ d.e : Nat) : Rat) := by
    rw [Rat.intCast_mul, Rat.intCast_natCast, Rat.div_def, Rat.div_def, Rat.mul_assoc,
      Rat.mul_comm ((10 ^ d.e : Nat) : Rat)⁻¹, ← Rat.mul_assoc]
  rw [this]
  exact roundFrac_spec' _ _ (pow10_pos _)

/-! ## Digits -/

theorem digitChar_isDigit : ∀ m, m < 10 → (digitChar m).isDigit = true := by decide
theorem digitVal_digitChar : ∀ m, m < 10 → digitVal (digitChar m) = m := by decide
theorem digitChar_ne_zero : ∀ m, m < 10 → 1 ≤ m → digitChar m ≠ '0' := by decide
theorem digitChar_zero : digitChar 0 = '0' := by decide

theorem natDigits_eq (n : Nat) :
    natDigits n = if n < 10 then [digitChar n] else natDigits (n / 10) ++ [digitChar (n % 10)] := by
  rw [natDigits]

theorem natDigits_ne_nil (n : Nat) : natDigits n ≠ [] := by
  rw [natDigits_eq]; split <;> simp

theorem natDigits_isDigit (n : Nat) : ∀ c ∈ natDigits n, c.isDigit = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natDigits_eq]
    split
    · simp only [List.mem_singleton]; intro c hc; subst hc; exact digitChar_isDigit n (by omega)
    · intro c hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | hc
      · exact ih (n / 10) (by omega) c hc
      · subst hc; exact digitChar_isDigit _ (Nat.mod_lt _ (by decide))

theorem digitsVal_append (l₁ l₂ : List Char) :
    digitsVal (l₁ ++ l₂) = digitsVal l₁ * 10 ^ l₂.length + digitsVal l₂ := by
  induction l₁ with
  | nil => simp [digitsVal]
  | cons c cs ih =>
    simp only [List.cons_append, digitsVal, ih, List.length_append, Nat.pow_add]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

theorem digitsVal_natDigits (n : Nat) : digitsVal (natDigits n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natDigits_eq]
    split
    · simp [digitsVal, digitVal_digitChar n (by omega)]
    · rw [digitsVal_append, ih (n / 10) (by omega)]
      simp [digitsVal, digitVal_digitChar _ (Nat.mod_lt n (by decide : 10 > 0))]
      omega

theorem natDigits_length (n k : Nat) (hk : 1 ≤ k) (h : n < 10 ^ k) : (natDigits n).length ≤ k := by
  induction n using Nat.strongRecOn generalizing k with
  | _ n ih =>
    rw [natDigits_eq]
    split
    · simp; omega
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : 1 ≤ j := by
        cases j with
        | zero => simp at h; omega
        | succ _ => omega
      rw [Nat.pow_succ] at h
      have := ih (n / 10) (by omega) j hj (by omega)
      simp; omega

theorem natDigits_head (n : Nat) (hn : 1 ≤ n) : (natDigits n).head? ≠ some '0' := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natDigits_eq]
    split
    · simp; exact digitChar_ne_zero n (by omega) hn
    · have hne := natDigits_ne_nil (n / 10)
      obtain ⟨c, cs, hc⟩ : ∃ c cs, natDigits (n / 10) = c :: cs := by
        cases h : natDigits (n / 10) with
        | nil => exact absurd h hne
        | cons c cs => exact ⟨c, cs, rfl⟩
      have := ih (n / 10) (by omega) (by omega)
      rw [hc] at this ⊢
      simpa using this

theorem natDigits_zero : natDigits 0 = ['0'] := by rw [natDigits_eq]; decide

theorem digitsVal_zeros (z : Nat) (l : List Char) :
    digitsVal (List.replicate z '0' ++ l) = digitsVal l := by
  induction z with
  | zero => simp
  | succ z ih =>
    simp only [List.replicate_succ, List.cons_append, digitsVal]
    rw [ih]; simp [digitVal]

theorem digitsAcc_eq (l : List Char) (acc : Nat) :
    digitsAcc l acc = acc * 10 ^ l.length + digitsVal l := by
  induction l generalizing acc with
  | nil => simp [digitsAcc, digitsVal]
  | cons c cs ih =>
    simp only [digitsAcc, ih, digitsVal, List.length_cons, Nat.pow_succ, digitVal]
    have : '0'.toNat = 48 := rfl
    rw [this]
    grind

/-! ## `fixed` produces a decimal literal denoting `k / 10ⁿ` -/

/-- The fraction digits `fixed` emits (empty when `n = 0`). -/
def fixedFrac (n : Nat) (k : Int) : List Char :=
  if n = 0 then [] else
    let frac := natDigits (k.natAbs % 10 ^ n)
    List.replicate (n - frac.length) '0' ++ frac

theorem fixedFrac_length (n : Nat) (k : Int) : (fixedFrac n k).length = n := by
  unfold fixedFrac
  split
  · simp; omega
  · have := natDigits_length (k.natAbs % 10 ^ n) n (by omega) (Nat.mod_lt _ (pow10_pos n))
    simp; omega

theorem fixedFrac_isDigit (n : Nat) (k : Int) : ∀ c ∈ fixedFrac n k, c.isDigit = true := by
  unfold fixedFrac
  split
  · simp
  · intro c hc
    simp only [List.mem_append, List.mem_replicate] at hc
    rcases hc with ⟨_, rfl⟩ | hc
    · decide
    · exact natDigits_isDigit _ c hc

theorem fixedFrac_val (n : Nat) (k : Int) : digitsVal (fixedFrac n k) = k.natAbs % 10 ^ n := by
  unfold fixedFrac
  split
  · subst_vars; simp [digitsVal, Nat.mod_one]
  · simp only; rw [digitsVal_zeros, digitsVal_natDigits]

theorem fixed_toList (n : Nat) (k : Int) :
    (fixed n k).toList =
      (if decide (k < 0) then ['-'] else []) ++ natDigits (k.natAbs / 10 ^ n) ++
      (if fixedFrac n k = [] then [] else '.' :: fixedFrac n k) := by
  unfold fixed
  rw [String.toList_ofList]
  by_cases hn : n = 0
  · simp [hn, fixedFrac]
  · have hne : fixedFrac n k ≠ [] := by
      intro h; have := fixedFrac_length n k; rw [h] at this; simp at this; omega
    simp only [hn, ite_false, hne, decide_eq_true_eq]
    unfold fixedFrac; simp [hn]

theorem fixed_declit (n : Nat) (k : Int) :
    DecLit (fixed n k) (decide (k < 0)) (natDigits (k.natAbs / 10 ^ n)) (fixedFrac n k) ∧
    DecLit.den (decide (k < 0)) (natDigits (k.natAbs / 10 ^ n)) (fixedFrac n k) = ⟨k, n⟩ := by
  refine ⟨⟨natDigits_ne_nil _, natDigits_isDigit _, fixedFrac_isDigit n k, fixed_toList n k⟩, ?_⟩
  unfold DecLit.den
  rw [digitsVal_append, digitsVal_natDigits, fixedFrac_val, fixedFrac_length,
    Nat.mul_comm, Nat.div_add_mod]
  by_cases hk : k < 0
  · simp [hk]; omega
  · simp [hk]; omega

/-! ## The parser -/

theorem takeWhile_dropWhile_app (p : Char → Bool) (a X : List Char)
    (ha : ∀ c ∈ a, p c = true) (hX : ∀ c t, X = c :: t → p c = false) :
    List.takeWhile p (a ++ X) = a ∧ List.dropWhile p (a ++ X) = X := by
  induction a with
  | nil =>
    cases X with
    | nil => simp
    | cons c t => have := hX c t rfl; simp [this]
  | cons c cs ih =>
    have hc := ha c (by simp)
    have := ih (fun x hx => ha x (by simp [hx]))
    simp [hc, this]

/-- Sign handling, as in `parseDec`. -/
def splitSign : List Char → Bool × List Char
  | '-' :: r => (true, r)
  | r => (false, r)

theorem splitSign_eq (l : List Char) :
    l = (if (splitSign l).1 then ['-'] else []) ++ (splitSign l).2 := by
  unfold splitSign; split <;> simp

/-- The body of `parseDec` after the sign, verbatim. -/
def parseBody (neg : Bool) (rest : List Char) : Option Dec :=
  let a := rest.takeWhile Char.isDigit
  if a.isEmpty then none else
  match rest.dropWhile Char.isDigit with
  | [] => some ⟨sgn neg * (digitsAcc a 0 : Int), 0⟩
  | '.' :: b =>
    if !b.isEmpty && b.all Char.isDigit then
      some ⟨sgn neg * (digitsAcc (a ++ b) 0 : Int), b.length⟩
    else none
  | _ => none

theorem parseDec_eq_body (s : String) :
    parseDec s = parseBody (splitSign s.toList).1 (splitSign s.toList).2 := by
  unfold parseDec parseBody splitSign
  generalize s.toList = l
  rcases l with _ | ⟨c, r⟩
  · rfl
  · by_cases hc : c = '-'
    · subst hc; rfl
    · simp [hc]
      generalize List.dropWhile Char.isDigit (c :: r) = T
      rcases T with _ | ⟨d, b⟩
      · rfl
      · by_cases hd : d = '.'
        · subst hd; rfl
        · simp [hd]

theorem mem_takeWhile {p : Char → Bool} {l : List Char} : ∀ c ∈ l.takeWhile p, p c = true := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    intro c hc
    by_cases hx : p x = true
    · simp [List.takeWhile, hx] at hc
      rcases hc with rfl | hc
      · exact hx
      · exact ih c hc
    · simp [List.takeWhile, hx] at hc

theorem sgn_eq (neg : Bool) : sgn neg = if neg then -1 else 1 := rfl

theorem parseBody_iff (neg : Bool) (rest : List Char) (d : Dec) :
    parseBody neg rest = some d ↔
      ∃ a b, a ≠ [] ∧ (∀ c ∈ a, c.isDigit = true) ∧ (∀ c ∈ b, c.isDigit = true) ∧
        rest = a ++ (if b = [] then [] else '.' :: b) ∧ d = DecLit.den neg a b := by
  constructor
  · intro h
    have hrest := (List.takeWhile_append_dropWhile (p := Char.isDigit) (l := rest)).symm
    unfold parseBody at h
    simp only at h
    split at h
    · exact absurd h (by simp)
    · rename_i hne
      have hne' : rest.takeWhile Char.isDigit ≠ [] := by simpa using hne
      split at h
      · rename_i hT
        refine ⟨_, [], hne', mem_takeWhile, by simp, by rw [hT] at hrest; simpa using hrest, ?_⟩
        simp at h; subst h
        simp [DecLit.den, digitsAcc_eq, sgn_eq]
      · rename_i b hT
        split at h
        · rename_i hb
          simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
            List.all_eq_true] at hb
          refine ⟨_, b, hne', mem_takeWhile, hb.2, ?_, ?_⟩
          · rw [hT] at hrest; simpa [hb.1] using hrest
          · simp at h; subst h
            simp [DecLit.den, digitsAcc_eq, sgn_eq]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  · rintro ⟨a, b, ha, hda, hdb, hrest, rfl⟩
    have key := takeWhile_dropWhile_app Char.isDigit a (if b = [] then [] else '.' :: b) hda
      (by
        intro c t h
        by_cases hb : b = []
        · simp [hb] at h
        · simp [hb] at h; rw [← h.1]; decide)
    subst hrest
    unfold parseBody
    simp only [key.1, key.2]
    have : a.isEmpty = false := by cases a <;> simp_all
    simp only [this, Bool.false_eq_true, ite_false]
    by_cases hb : b = []
    · subst hb; simp [DecLit.den, digitsAcc_eq, sgn_eq]
    · simp only [hb, ite_false]
      have hb' : (!b.isEmpty && b.all Char.isDigit) = true := by
        simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true]
        exact ⟨hb, hdb⟩
      simp only [hb', ite_true]
      simp [DecLit.den, digitsAcc_eq, sgn_eq]

theorem parseDec_iff' (s : String) (d : Dec) :
    parseDec s = some d ↔ ∃ neg a b, DecLit s neg a b ∧ d = DecLit.den neg a b := by
  rw [parseDec_eq_body, parseBody_iff]
  constructor
  · rintro ⟨a, b, ha, hda, hdb, hrest, hd⟩
    refine ⟨(splitSign s.toList).1, a, b, ⟨ha, hda, hdb, ?_⟩, hd⟩
    rw [List.append_assoc, ← hrest]
    exact splitSign_eq s.toList
  · rintro ⟨neg, a, b, ⟨ha, hda, hdb, hs⟩, hd⟩
    have hsplit : splitSign s.toList = (neg, a ++ (if b = [] then [] else '.' :: b)) := by
      rw [hs]
      cases neg
      · obtain ⟨c, a', rfl⟩ : ∃ c a', a = c :: a' := by
          cases a with
          | nil => exact absurd rfl ha
          | cons c a' => exact ⟨c, a', rfl⟩
        have hc : c ≠ '-' := by
          intro h; have := hda c (by simp); subst h; simp at this
        simp only [Bool.false_eq_true, ite_false, List.nil_append, List.cons_append]
        unfold splitSign; simp [hc]
      · simp [splitSign]
    rw [hsplit]
    exact ⟨a, b, ha, hda, hdb, rfl, hd⟩

theorem fixed_shape' (n : Nat) (k : Int) : FixedShape n (fixed n k) := by
  refine ⟨_, _, _, (fixed_declit n k).1, fixedFrac_length n k, ?_⟩
  by_cases hq : k.natAbs / 10 ^ n = 0
  · left; rw [hq, natDigits_zero]
  · right; exact natDigits_head _ (Nat.pos_of_ne_zero hq)

theorem fixed_neg' (n : Nat) (k : Int) :
    (fixed n k).toList.head? = some '-' ↔ k < 0 := by
  rw [fixed_toList]
  by_cases hk : k < 0
  · simp [hk]
  · obtain ⟨c, cs, hc⟩ : ∃ c cs, natDigits (k.natAbs / 10 ^ n) = c :: cs := by
      cases h : natDigits (k.natAbs / 10 ^ n) with
      | nil => exact absurd h (natDigits_ne_nil _)
      | cons c cs => exact ⟨c, cs, rfl⟩
    have hdig := natDigits_isDigit (k.natAbs / 10 ^ n) c (by rw [hc]; simp)
    have : c ≠ '-' := by intro h; subst h; simp at hdig
    simp [hk, hc, this]

theorem parseDec_fixed' (n : Nat) (k : Int) : parseDec (fixed n k) = some ⟨k, n⟩ :=
  (parseDec_iff' _ _).2 ⟨_, _, _, (fixed_declit n k).1, (fixed_declit n k).2.symm⟩
