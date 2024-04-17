import Lean
open Lean Elab Command Term Meta

syntax (name := instantiate) "instantiate" "?" ident ":=" term : tactic

@[tactic_elab instantiate]
def instantateM : Tactic.TacticM Unit := fun ctx => do
  return ()


section manual

variable (n m k: Nat)

def p :=  k * (n + m)


def is_correct: (k * n) + (k * m) = p n m k := by
  simp_all [p, Nat.mul_add]
  
def is_correct_synth: (k * n) + (k * m) = ?mp := by
  instantiate ?mp := p n m k
  
  simp_all [p, Nat.mul_add]


end manual



