import Lean
import DerivingSuchThat
open Lean Elab Command Term Meta


section manual

variable (n m k: Nat)

derive p such that (k * n) + (k * m) = p as h := by
   instantiate ?p := k * (n + m)
   simp [p, Nat.mul_add]

#eval (p 1 2 3)

end manual



