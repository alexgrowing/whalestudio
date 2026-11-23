import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.Pinch

def IsSecFam {X : Scheme.{0}} (L : LB X) {J : Type} (D : J → X.Opens) (k : J → L.ι)
    (hD : ∀ j, D j ≤ L.U (k j)) (e : ∀ j, Γ(X, D j)) : Prop :=
  ∀ (j j' : J) (z : X) (hz : z ∈ D j) (hz' : z ∈ D j'),
    (X.presheaf.germ (D j) z hz).hom (e j) =
      (X.presheaf.germ (L.U (k j) ⊓ L.U (k j')) z ⟨hD j hz, hD j' hz'⟩).hom (L.g (k j) (k j')).val *
        (X.presheaf.germ (D j') z hz').hom (e j')

end GlobalTheory.Pinch
