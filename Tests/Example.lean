import Lean
import DerivingSuchThat
open Lean Elab Command Term Meta


section manual

variable (n m k: Nat)

-- Witness chosen with `show` (which unifies it), proof by `simp`; section
-- variables `n m k` are abstracted into `p` and `h`.
derive p such that (k * n) + (k * m) = p as h := by
   show (k * n) + (k * m) = k * (n + m)
   simp [Nat.mul_add]

-- `p` and its proof `h` are real, usable definitions.
example (n m k : Nat) : (k * n) + (k * m) = p n m k := h n m k

end manual


section synthesis

-- Witness pinned purely by unification in the proof; the fix writes the
-- synthesised witness back into `def five`.
derive five such that (5 = five) as five_eq := by rfl

example : five = 5 := five_eq.symm

end synthesis
