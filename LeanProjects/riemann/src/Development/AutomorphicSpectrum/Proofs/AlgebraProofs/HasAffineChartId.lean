import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.FreeQuotProof

def HasAffineChart {P X : Scheme.{0}} (a b : P ⟶ X) (V : X.Opens) : Prop :=
  a ⁻¹ᵁ V = b ⁻¹ᵁ V ∧
    ∃ (Y : Scheme.{0}) (q : V.toScheme ⟶ Y) (a' : (b ⁻¹ᵁ V).toScheme ⟶ V.toScheme),
      IsAffine Y ∧ IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
        a' ≫ V.ι = (b ⁻¹ᵁ V).ι ≫ a ∧ IsPullback a' (b ∣_ V) q q

end GlobalTheory.CompanionTheory.FreeQuotProof
