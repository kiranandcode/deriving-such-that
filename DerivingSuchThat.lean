import Lean
import DerivingSuchThat.Utils
import DerivingSuchThat.ProgramAndProof
open Lean Elab Command Term Meta

declare_syntax_cat proofs
syntax "by" tacticSeq : proofs
syntax "by" : proofs
syntax term : proofs

elab "add_goal" "?" hvar:ident ts:proofs : tactic =>
   match ts with
   | `(proofs| by) => do
      let Option.some mvar <- findMVarByName hvar.getId | throwErrorAt hvar "{hvar.getId} does not match to any known metavariable"
      Tactic.appendGoals [mvar]
      Tactic.withMainContext $ Tactic.closeUsingOrAdmit $ Tactic.evalTactic (<- `(tactic| skip))
      return ()
   | `(proofs| by $ts:tacticSeq) => do
      let Option.some mvar <- findMVarByName hvar.getId | throwErrorAt hvar "{hvar.getId} does not match to any known metavariable"
      Tactic.appendGoals [mvar]
      Tactic.withMainContext do Tactic.evalTactic ts
      return ()
   | `(proofs| $stx:term) => do
      let Option.some mvar <- findMVarByName hvar.getId | throwErrorAt hvar "{hvar.getId} does not match to any known metavariable"
      Tactic.appendGoals [mvar]
      Tactic.evalTactic (<- `(tactic| exact $stx))
   | _ => throwErrorAt ts "unsupported syntax"


syntax "instantiate" "?" ident ":=" term : tactic

elab_rules : tactic
| `(tactic| instantiate ? $hvar:ident := $t:term) => do
   let Option.some mvar <- findMVarByName hvar.getId | throwErrorAt hvar "{hvar.getId} does not match to any known metavariable"
   mvar.assign (<- elabTerm t none)
   return ()

syntax (name := derive_such_that) "derive " ident " such that " term (" as " ident)? " := " proofs : command

@[command_elab derive_such_that]
def deriveSuchThat : CommandElab := fun stx => do
   match stx with
   | `(command| derive $id:ident such that $prop:term := $proof:proofs) =>
     elabCommand <|
        <- `(def $id := ?$id
             where goal : True :=
                 let $id := ?$id
                 let goal : $prop := by
                   add_goal ?$id $proof
                 True.intro)
   | `(command| derive $id:ident such that $prop:term as $propName:ident := $proof:proofs ) =>
     let result <- mkFreshIdent id
     let bindings <- runTermElabM fun xs => do
          xs.mapM fun v => liftMetaM (getFvarUserName v)
     let original_id := id
     elabCommand <|
        <- `(private def $result :=
               let $id := ?$id
               let goal : $prop := by
                    skip
                    add_goal ?$original_id $proof
               ProgramAndProof.intro $id goal
             def $id := ProgramAndProof.program ($result $bindings*)
             def $propName := ProgramAndProof.proof ($result $bindings*))
   | _ => throwErrorAt stx "Invalid syntax for derive such that"
