import LakeLevel
import Lean

/-!
# Proof audit

For every theorem in the `LakeLevel` namespace, ask the kernel which axioms it
ultimately depends on. A theorem depending on `sorryAx` is **not proved**.
A dependency on anything outside the standard three is a red flag
(e.g. `Lean.ofReduceBool` would mean the compiler was trusted to decide a goal).

Run with: `lake env lean scripts/Audit.lean`
Exits non-zero unless every theorem is fully proved from standard axioms.
-/

open Lean Elab Command

def standardAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

elab "#audit" : command => do
  let env ← getEnv
  let mut proved : Nat := 0
  let mut unproved : Array Name := #[]
  let mut suspicious : Array (Name × List Name) := #[]
  let mut sorriedDefs : Array Name := #[]
  -- Only theorems *we wrote*, i.e. those living in LakeLevel.Proofs.* modules,
  -- not the injectivity/sizeOf lemmas Lean auto-generates for every structure.
  -- Definitions are checked in every LakeLevel module.
  let inModule (n : Name) (pre : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some i => pre.isPrefixOf env.header.moduleNames[i.toNat]!
    | none => false
  let autoGen (n : Name) : Bool :=
    match n with
    | .str _ s => s.startsWith "eq_" || s == "injEq" || s == "inj" || s == "sizeOf_spec"
    | _ => false
  let decls := env.constants.map₁.toList.filter fun (n, ci) =>
    (`LakeLevel).isPrefixOf n && !n.isInternal && !autoGen n &&
    (match ci with
     | .thmInfo _ => inModule n `LakeLevel.Proofs
     | _ => inModule n `LakeLevel)
  for (n, ci) in decls.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    let axs ← liftCoreM (collectAxioms n)
    let axs := axs.toList
    match ci with
    | .thmInfo _ =>
      if axs.contains ``sorryAx then unproved := unproved.push n
      else if axs.any (!standardAxioms.contains ·) then
        suspicious := suspicious.push (n, axs.filter (!standardAxioms.contains ·))
      else proved := proved + 1
    | .defnInfo _ =>
      if axs.contains ``sorryAx then sorriedDefs := sorriedDefs.push n
    | _ => pure ()
  logInfo m!"theorems proved from standard axioms only: {proved} (obligations + helper lemmas)"
  -- The obligations are frozen in scripts/obligations.txt (generated from tag stage-3).
  -- Each must still exist, still be a theorem, and be fully proved: deleting or
  -- weakening-by-removal a hard theorem cannot turn the audit green.
  let names := (← IO.FS.lines "scripts/obligations.txt").filter (· ≠ "")
  let mut missing : Array String := #[]
  let mut obligationsProved : Nat := 0
  for s in names do
    let n := s.toName
    match env.find? n with
    | some (.thmInfo _) =>
      let axs ← liftCoreM (collectAxioms n)
      if axs.all (standardAxioms.contains ·) then obligationsProved := obligationsProved + 1
    | _ => missing := missing.push s
  logInfo m!"obligations (scripts/obligations.txt) fully proved: {obligationsProved}/{names.size}"
  unless missing.isEmpty do logInfo m!"OBLIGATIONS MISSING: {missing.toList}"
  logInfo m!"theorems still depending on sorry: {unproved.size}{if unproved.isEmpty then m!"" else m!"\n  " ++ m!"{unproved.toList}"}"
  logInfo m!"definitions still depending on sorry: {sorriedDefs.size}{if sorriedDefs.isEmpty then m!"" else m!"\n  " ++ m!"{sorriedDefs.toList}"}"
  unless suspicious.isEmpty do logInfo m!"NON-STANDARD AXIOMS: {suspicious.toList}"
  if !unproved.isEmpty || !suspicious.isEmpty || !sorriedDefs.isEmpty || !missing.isEmpty ||
      obligationsProved != names.size then
    throwError "audit failed"

#audit
