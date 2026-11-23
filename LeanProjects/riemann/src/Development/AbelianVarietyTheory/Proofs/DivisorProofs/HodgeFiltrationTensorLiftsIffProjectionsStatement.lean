import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationTensorLiftsIffProjections
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeFiltration_tensor_lifts_iff_projections : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀)
    (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (X Y : Over (Sp R)) (i : A₀.left ⟶ X.left) (j : B₀.left ⟶ Y.left)
    (wi : i ≫ X.hom = A₀.hom ≫ spMap π) (wj : j ≫ Y.hom = B₀.hom ≫ spMap π)
    (e : Sp R ⟶ X.left) (e' : Sp R ⟶ Y.left), e ≫ X.hom = 𝟙 _ → e' ≫ Y.hom = 𝟙 _ →
    (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ B₀).left ≫ j = spMap π ≫ e' →
    ∀ (l : (A₀ ⊗ B₀).left ⟶ (X ⊗ Y).left), l ≫ (fst X Y).left = (fst A₀ B₀).left ≫ i → l ≫ (snd X Y).left = (snd A₀ B₀).left ≫ j →
    ∀ (wl : l ≫ (X ⊗ Y).hom = (A₀ ⊗ B₀).hom ≫ spMap π) (d : Crys κ (spMap π) (A₀ ⊗ B₀)),
    d ∈ schemeFil κ (A₀ ⊗ B₀) (X ⊗ Y) l wl ↔
      push κ (spMap π) (fst A₀ B₀) d ∈ schemeFil κ A₀ X i wi ∧ push κ (spMap π) (snd A₀ B₀) d ∈ schemeFil κ B₀ Y j wj := by
  first | exact @GlobalTheory.SqLift.ProdFil.schemeFil_tensor_iff | exact GlobalTheory.SqLift.ProdFil.schemeFil_tensor_iff | (intros; apply GlobalTheory.SqLift.ProdFil.schemeFil_tensor_iff <;> assumption)
