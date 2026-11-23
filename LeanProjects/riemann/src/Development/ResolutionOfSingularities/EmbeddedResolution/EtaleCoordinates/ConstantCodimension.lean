import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def HasEtaleCoordCodim {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') (c : ℕ) : Prop :=
  ∀ x : X, ∃ (U : X'.Opens) (_ : τ.base x ∈ U) (m : ℕ) (ch : EtaleChart p U m)
    (S : Finset (Fin m)), S.card = c ∧ restrictIdeal τ.ker U = ch.coordIdeal S

end FunctorialResolution.EmbeddedResolution
