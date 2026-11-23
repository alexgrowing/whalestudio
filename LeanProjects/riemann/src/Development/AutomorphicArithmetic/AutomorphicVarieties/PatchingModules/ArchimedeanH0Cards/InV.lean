import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality

namespace UpperTheory.V.Pa.B2

variable {l : ℕ} [Fact l.Prime] {L : Loc} (G : Glob l L)

def inV (v : L.Vl) : (plOf G).ι := Sum.inl v

def inU (u : L.St) : (plOf G).ι := Sum.inr u

end UpperTheory.V.Pa.B2
