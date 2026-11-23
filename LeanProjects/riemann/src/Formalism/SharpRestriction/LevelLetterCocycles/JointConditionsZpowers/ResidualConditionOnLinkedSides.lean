import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

open scoped Pointwise

def GlobalDatumLocalisationCondition (D : D7) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (s : D.ntw.Sig i) k, D.host.g k ≠ D.ntw.l i → ∀ v ∈ placesOver D.host.E (D.host.g k),
    ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
      ∀ σ : G D.host.E D.nd.Om, Formalism.MainNotions.BlochKatoReduction.IsWild A σ → Formalism.MainNotions.BlochKatoReduction.Gen.rbar D.ntw i s σ = 1

def ValuationStabilityUnlinkedSides (D : D7) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ∀ s : D.ntw.Sig i, ¬ SideLoc D i (D.ntw.side i s) → Formalism.MainNotions.BlochKatoReduction.Gen.ValuationStabilityAtRing D.ntw i s

end Formalism.MainNotions.N
