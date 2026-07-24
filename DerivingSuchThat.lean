import Lean
import DerivingSuchThat.Utils
import DerivingSuchThat.ProgramAndProof
open Lean Elab Command Term Meta

/-!
# `derive … such that …`

`derive x such that P x := by tac` synthesises a term `x` together with a proof
of `P x`, then emits both as real definitions: `def x` (and, with `as h`,
`def h : P x`).  In-scope section `variable`s are abstracted into both.

The proof of `P x` is elaborated *at the goal type* with `x` an open
metavariable, so:

  * a proof that pins `x` by unification — an `apply`/`exact`/`show`/`rfl` chain
    — fills it automatically (this is the synthesis mode); and
  * the witness is written back into `def x` (the earlier implementation left it
    unassigned, so extraction silently failed for unification-synthesised
    witnesses).
-/

declare_syntax_cat proofs
syntax "by " tacticSeq : proofs
syntax "by" : proofs
syntax term : proofs

private def proofToTerm : TSyntax `proofs → TermElabM (TSyntax `term)
  | `(proofs| by $ts:tacticSeq) => `(by $ts:tacticSeq)
  | `(proofs| by)               => `(by skip)
  | `(proofs| $t:term)          => pure t
  | _                           => throwError "derive: unsupported proof syntax"

syntax (name := derive_such_that)
  "derive " ident " such" " that " term (" as " ident)? " := " proofs : command

@[command_elab derive_such_that]
def deriveSuchThat : CommandElab := fun stx => do
  match stx with
  | `(command| derive $id:ident such that $prop:term $[as $pn?:ident]? := $pf:proofs) =>
    -- `runTermElabM` brings section `variable`s into scope and hands them back
    -- as `fvars`, which we abstract into the emitted definitions.
    Command.runTermElabM fun fvars => do
      -- `fun x => P x`  gives the witness type `T` from `T → Prop`.
      let pred ← Term.elabTerm (← `(fun $id:ident => $prop)) none
      Term.synthesizeSyntheticMVarsNoPostponing
      let pred ← instantiateMVars pred
      let witnessType ← match ← whnf (← inferType pred) with
        | .forallE _ t _ _ => pure t
        | _ => throwError "derive: `{prop}` is not a predicate in `{id}`"
      -- Single witness metavariable; the proof, elaborated at the goal type,
      -- assigns it (by unification / `show` / `exact`).
      let witnessMVar ← mkFreshExprMVar witnessType (userName := id.getId)
      let goalType ← instantiateMVars (pred.beta #[witnessMVar])
      -- `withSynthesize` runs the full synthetic-mvar pass the proof needs — in
      -- particular, holes like `netk := fun _ => _` in an `apply` chain are only
      -- resolved by this final pass, not by `elabTermEnsuringType` alone.
      let proof ← Term.withSynthesize <|
        Term.elabTermEnsuringType (← proofToTerm pf) goalType
      Term.synthesizeSyntheticMVarsNoPostponing
      let proof ← instantiateMVars proof
      let witness ← instantiateMVars witnessMVar
      if witness.hasExprMVar then
        throwError "derive: witness for `{id}` underdetermined:{indentExpr witness}"
      -- Emit `def id := witness` and (with `as h`) `def h : P id := proof`,
      -- abstracting the section variables.  Abstracting a typed section variable
      -- (e.g. `G : Type`) can leave an under-constrained universe metavariable
      -- (which `instantiateMVars`/`hasExprMVar` ignore); `levelMVarToParam`
      -- generalises those into universe parameters so the declaration is
      -- kernel-valid.
      let mkDef (name : Name) (type value : Expr) : TermElabM Unit := do
        let value ← Term.levelMVarToParam (← instantiateMVars (← mkLambdaFVars fvars value))
        let type  ← Term.levelMVarToParam (← instantiateMVars (← mkForallFVars fvars type))
        let params := (Lean.collectLevelParams (Lean.collectLevelParams {} value) type).params
        addDecl <| .defnDecl {
          name, levelParams := params.toList, type, value,
          hints := .opaque, safety := .safe, all := [name] }
      -- Declare under the current namespace (not the root).
      let ns ← getCurrNamespace
      mkDef (ns ++ id.getId) (← instantiateMVars witnessType) witness
      if let some pn := pn? then
        mkDef (ns ++ pn.getId) (← instantiateMVars goalType) proof
  | _ => throwErrorAt stx "Invalid syntax for derive such that"
