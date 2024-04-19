import Lean
open Lean Elab Command Term Meta

def findMVarByName (name : Name) : Tactic.TacticM (Option MVarId) := do
   let mctx <- getMCtx
   for ⟨mvar, mdecl⟩ in mctx.decls do
     let userName := mdecl.userName
     if userName == name then
       return mvar
   return none

def getFvarUserName (e : Expr) := do
    let fvarId := e.fvarId!
    let ident <- fvarId.getUserName
    return mkIdent ident



