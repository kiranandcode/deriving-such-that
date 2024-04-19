inductive ProgramAndProof (T: Type) (P: Prop)
| intro (t : T) (p : P)

namespace ProgramAndProof

def program {T : Type} {P : Prop} : ProgramAndProof T P -> T | ProgramAndProof.intro l _ => l
def proof {T : Type} {P : Prop} : ProgramAndProof T P -> P | ProgramAndProof.intro _ r => r

end ProgramAndProof
