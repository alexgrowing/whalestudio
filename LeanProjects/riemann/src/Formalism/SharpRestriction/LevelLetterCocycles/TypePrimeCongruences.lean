import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.LevelLetterCocycles.AutomorphicSideWildInertia

noncomputable section

namespace Formalism.MainNotions.TypePrimeCongruences

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

def TypePrimeChoiceConclusions (D : D7) : Prop := @PairedCharacterCondition.TypePrimeChoiceLemmas D

def TypePrimeWildIdempotentChoice (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → HG D.nd D.naut i →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r →
    ∀ π ∈ D.nd.Z i, TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → PairedCharacterCondition.WildIdempotentChoice i r ρ π

def TypePrimeHypotheses (D : D7) : Prop := SumRepresentations.adm5 D ∧ SumRepresentations.Conclusion41 D ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D ∧ TypePrimeWildIdempotentChoice D

def TypePrimeConclusionsOfHypotheses (D : D7) : Prop := TypePrimeHypotheses D → TypePrimeChoiceConclusions D

end Formalism.MainNotions.TypePrimeCongruences
