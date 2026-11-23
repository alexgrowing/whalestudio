import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalRingCardinality.DataRows

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceMapping

def ThetaPMapsEigenspaceInto {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (x : N.X i), x ∈ ZgoodN N A i →
    ∀ Sig : List (Formalism.BasicNotions.Part A.CG), HasParamX N A i x Sig →
      ∀ F ∈ eigC N A i x, what₂.thetaP (N.mu i) (N.j i) F ∈ MjSig N A i Sig

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceMapping
