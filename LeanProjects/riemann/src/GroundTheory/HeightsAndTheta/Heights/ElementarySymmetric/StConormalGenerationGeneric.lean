import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StJacobianRankGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

def ConormalGenerationGeneric.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] (ι : Type) [Fintype ι]
    (f : ι → MvPolynomial (Fin n) ℂ),
    (∀ i, f i ∈ J) →
    Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) (Set.range (genericGradient J ∘ f)) =
      Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) (genericGradient J '' (J : Set _)) →
    ∃ s : MvPolynomial (Fin n) ℂ, s ∉ J ∧ ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)

end

end GroundTheory.Heights₂.Heights
