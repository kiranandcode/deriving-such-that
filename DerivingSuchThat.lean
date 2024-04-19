import Lean
import DerivingSuchThat.Utils
import DerivingSuchThat.ProgramAndProof

open Lean Elab Command Term Meta


syntax "instantiate" "?" ident ":=" term : tactic

elab_rules : tactic
| `(tactic| instantiate ? $hvar:ident := $t:term) => do
   let Option.some mvar <- findMVarByName hvar.getId | throwErrorAt hvar "{hvar.getId} does not match to any known metavariable"
   mvar.assign (<- elabTerm t none)
   return ()

syntax (name := derive_such_that) "derive " ident " such that " term (" as " ident)? " := " term : command

@[command_elab derive_such_that]
def deriveSuchThat : CommandElab := fun stx => do
   match stx with
   | `(command| derive $id:ident such that $prop:term := $proof:term) =>
     elabCommand <|
        <- `(def $id := ?$id
             where goal : True :=
                 let $id := ?$id
                 let goal : $prop := $proof
                 True.intro)
   | `(command| derive $id:ident such that $prop:term as $propName:ident := $proof:term) =>
     let result <- mkFreshIdent id
     let bindings <- runTermElabM fun xs => do
          xs.mapM fun v => liftMetaM (getFvarUserName v)
     elabCommand <|
        <- `(private def $result :=
               let $id := ?$id
               let goal : $prop := $proof
               ProgramAndProof.intro $id goal
             def $id := ProgramAndProof.program ($result $bindings*)
             def $propName := ProgramAndProof.proof ($result $bindings*))
   | _ => throwErrorAt stx "Invalid syntax for derive such that"
