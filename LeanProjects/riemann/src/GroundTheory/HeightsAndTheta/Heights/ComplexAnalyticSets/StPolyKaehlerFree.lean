import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def PolyKaehlerFree.Statement : Prop :=
  ∀ (R k : Type) [Field R] [Field k] [Algebra R k] (n : ℕ),
    Module.Free (MvPolynomial (Fin n) k) Ω[MvPolynomial (Fin n) k⁄R]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
