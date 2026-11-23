import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal

open NumberField IsDedekindDomain

def JointConditionTame (D : D7) (i : D.nd.Loc) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.E),
    (v ∈ D.nd.Q i ∨ (v ∈ D.nd.S i ∧ (v ∈ placesOver D.host.E D.host.pde ∨
      (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde')))) →
    ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 v), D.nd.chi i 1 σ = 1

end Formalism.MainNotions.N
