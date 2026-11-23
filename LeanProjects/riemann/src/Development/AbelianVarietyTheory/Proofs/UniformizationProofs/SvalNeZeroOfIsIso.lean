import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNeZeroIffSvalGenericPointNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem gs_eq_stalkMap_gs_id {Y Y' : Scheme.{0}} (τ : Y' ⟶ Y) (y : Y') (U : Y.Opens) (hy : τ y ∈ U) (a : Γ(Y, U)) :
    gs τ y U a = (τ.stalkMap y).hom (gs (𝟙 Y) (τ y) U a) := by
  have e : gs (𝟙 Y) (τ y) U a = (Y.presheaf.germ U (τ y) hy).hom a := gs_eq (𝟙 Y) (τ y) U hy a
  rw [e, gs_eq τ y U hy]
  exact (Scheme.Hom.germ_stalkMap_apply τ U y hy a).symm

theorem sval_ne_zero_of_isIso : ∀ (X Y : Scheme.{0}) [IsIntegral Y] (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L φ ε)), (∃ j, s.f j ≠ 0) → ∀ (Y' : Scheme.{0}) (τ : Y' ⟶ Y) [IsIso τ] (y : Y') (J), Good L y J → sval s τ y J ≠ 0 := by
  intro X Y _ L hL K _ φ ε s hs Y' τ _ y J hJ h0
  have hG : Good L (τ y) (fun χ : Y ⟶ X => J (τ ≫ χ)) := fun χ => hJ (τ ≫ χ)
  have h1 := (exists_ne_zero_iff_sval_ne_zero s hG).1 hs
  rw [sval_of s (𝟙 Y) (τ y) _ (fun k => J (τ ≫ φ k)) (fun k => by rw [Category.id_comp])] at h1
  apply h1
  have h2 : gs τ y (LB.wchart L φ (fun k => J (τ ≫ φ k))) (s.f (fun k => J (τ ≫ φ k))) = 0 := h0
  have h3 := (gs_eq_stalkMap_gs_id τ y _ (hJ.mem φ τ) _).symm.trans h2
  have hinj : Function.Injective (τ.stalkMap y).hom :=
    (ConcreteCategory.bijective_of_isIso (τ.stalkMap y)).1
  exact (map_eq_zero_iff _ hinj).1 h3

end GlobalTheory
