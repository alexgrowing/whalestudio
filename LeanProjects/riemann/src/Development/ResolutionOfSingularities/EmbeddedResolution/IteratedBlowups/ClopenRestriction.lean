import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def StrictNormalCrossingsRestrictToClopen : Prop :=
  ∀ (k : Type u) [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] (E : List W.IdealSheafData) (Z : W.IdealSheafData),
    InStrictNormalCrossingPosition p E → HasStrictNormalCrossingsWith p Z E →
    ∀ U : (Z.subscheme).Opens, IsClosed (U : Set ↥(Z.subscheme)) →
    (∀ D ∈ E, ∀ T ∈ irreducibleComponents (↥(U.toScheme)),
        ¬ ((U.ι ≫ Z.subschemeι).base '' T) ⊆ (D.support : Set ↥W)) →
    IsStrictNormalCrossingsDivisor ((E.prod.comap (U.ι ≫ Z.subschemeι)).radical)

end FunctorialResolution.EmbeddedResolution
