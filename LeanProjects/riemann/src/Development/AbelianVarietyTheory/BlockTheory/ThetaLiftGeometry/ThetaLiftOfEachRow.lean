import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N

def EachRowHasThetaLift {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∃ P : A.AV i, thetaOf N A i σ P

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent
