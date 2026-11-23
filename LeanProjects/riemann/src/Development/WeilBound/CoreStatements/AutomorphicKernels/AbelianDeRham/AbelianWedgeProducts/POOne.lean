import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianPullbackLattices.CompositeRestrictionPullInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Pf.WedgeProjections

variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]

theorem pO_one {Y : Over (Sp R)} (x : HO1 A.hom) : AXO.pO (1 : Y ⟶ A) x = 0 := by
  rw [Hom.one_def, AXO.pO_comp, AXO.HO1_base_eq_zero (AXO.pO _ x), map_zero]

theorem pO_mul (hAx : AxOSt) (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    AXO.pO (fst A A * snd A A) = AXO.pO (fst A A) + AXO.pO (snd A A) := by
  have e1 : lift (𝟙 A) (1 : A ⟶ A) ≫ (fst A A * snd A A) = 𝟙 A := by
    rw [Hom.mul_def, ← Category.assoc, comp_lift, lift_fst, lift_snd, ← Hom.mul_def, _root_.mul_one]
  have e2 : lift (1 : A ⟶ A) (𝟙 A) ≫ (fst A A * snd A A) = 𝟙 A := by
    rw [Hom.mul_def, ← Category.assoc, comp_lift, lift_fst, lift_snd, ← Hom.mul_def, _root_.one_mul]
  apply LinearMap.ext
  intro x
  rw [LinearMap.add_apply]
  have hc := hAx R A g hA hg
    (AXO.pO (fst A A * snd A A) x - AXO.pO (fst A A) x - AXO.pO (snd A A) x)
    ((AXO.pO_spec (lift (𝟙 A) (1 : A ⟶ A)) _ _).2 ?_) ((AXO.pO_spec (lift (1 : A ⟶ A) (𝟙 A)) _ _).2 ?_)
  · rw [sub_sub, sub_eq_zero] at hc
    exact hc
  · rw [map_sub, map_sub, ← AXO.pO_comp, ← AXO.pO_comp, ← AXO.pO_comp, e1, lift_fst, lift_snd,
      AXO.pO_id, pO_one A, sub_self, sub_zero]
  · rw [map_sub, map_sub, ← AXO.pO_comp, ← AXO.pO_comp, ← AXO.pO_comp, e2, lift_fst, lift_snd,
      AXO.pO_id, pO_one A, sub_zero, sub_self]

theorem r11 : AXO.pO (lift (𝟙 A) (1 : A ⟶ A)) ∘ₗ AXO.pO (fst A A) = LinearMap.id :=
  LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, ← AXO.pO_comp, lift_fst, AXO.pO_id]; rfl

theorem r12 : AXO.pO (lift (𝟙 A) (1 : A ⟶ A)) ∘ₗ AXO.pO (snd A A) = 0 :=
  LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, ← AXO.pO_comp, lift_snd, pO_one]; rfl

theorem r21 : AXO.pO (lift (1 : A ⟶ A) (𝟙 A)) ∘ₗ AXO.pO (fst A A) = 0 :=
  LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, ← AXO.pO_comp, lift_fst, pO_one]; rfl

theorem r22 : AXO.pO (lift (1 : A ⟶ A) (𝟙 A)) ∘ₗ AXO.pO (snd A A) = LinearMap.id :=
  LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, ← AXO.pO_comp, lift_snd, AXO.pO_id]; rfl

end MainStatements.Hodge.Pf.WedgeProjections
