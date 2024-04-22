import Lean
import DerivingSuchThat
open Lean Elab Command Term Meta


section manual

variable (n m k: Nat)

derive p such that (k * n) + (k * m) = p as h := by
   case p => exact k * (n + m)
   simp [p, Nat.mul_add]


end manual



