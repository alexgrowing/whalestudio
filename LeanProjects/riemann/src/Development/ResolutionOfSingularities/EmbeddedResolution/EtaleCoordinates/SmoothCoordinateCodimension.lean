import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def HasSmoothCoordCodim {X Y : Scheme.{u}} {k : Type u} [Field k]
    (s : Y ⟶ Spec (CommRingCat.of k)) (t : X ⟶ Y) (c : ℕ) : Prop :=
  ∀ x : X, ∃ (U : Y.Opens) (_ : t.base x ∈ U)
    (q : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c))),
    AlgebraicGeometry.Smooth q ∧
      q ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) = U.ι ≫ s ∧
      restrictIdeal t.ker U = (coordSubspaceIdeal k c Finset.univ).comap q

theorem hasSmoothCoordCodim_iff {X Y : Scheme.{u}} {k : Type u} [Field k]
    (s : Y ⟶ Spec (CommRingCat.of k)) (t : X ⟶ Y) (c : ℕ) :
    HasSmoothCoordCodim s t c ↔
      ∀ x : X, ∃ (U : Y.Opens) (_ : t.base x ∈ U)
        (q : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c))),
        AlgebraicGeometry.Smooth q ∧
          q ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) = U.ι ≫ s ∧
          restrictIdeal t.ker U = (coordSubspaceIdeal k c Finset.univ).comap q :=
  Iff.rfl

end FunctorialResolution.EmbeddedResolution

end
