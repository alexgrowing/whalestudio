import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal

namespace Formalism.L2.Pj

def ComplSt : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W],
    ∃ (T : CDVR) (ι : W →+* T.V), IsLocalHom ι ∧ ∃ ϖ : W, Irreducible ϖ ∧ Irreducible (ι ϖ)

end Formalism.L2.Pj
