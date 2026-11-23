import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareAffineH1Vanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesVanishingNoetherianAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeNoPrimitiveO2Statement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem pO1_comp {R : Type} [CommRing R] {Z Y A : Over (Sp R)} (i : Z ⟶ Y) (f : Y ⟶ A) (x : HO1 A.hom) :
    pO1 i (pO1 f x) = pO1 (i ≫ f) x :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).1 _ _ _ _ _ _ _ _ (ovw f) _ _ _ _ _ (ovw i) _ _ (ovw (i ≫ f)) (Over.comp_left _ _ _ _ _)
    (fun _ ↦ rfl)).1 x

theorem pO1_id {R : Type} [CommRing R] {A : Over (Sp R)} (x : HO1 A.hom) : pO1 (𝟙 A) x = x :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.2 R A).1 x

theorem pO1_unit_eq_zero {R : Type} [CommRing R] (x : HO1 (𝟙_ (Over (Sp R))).hom) : x = 0 := by
  have : IsAffine (𝟙_ (Over (Sp R))).left := by
    change IsAffine (Sp R); infer_instance
  exact (GlobalTheory.Obs.sq_abelian_and_affine_H1 R).2 _ _ x

theorem pO1_toUnit_comp {R : Type} [CommRing R] {Y A : Over (Sp R)} (f : 𝟙_ (Over (Sp R)) ⟶ A) (x : HO1 A.hom) :
    pO1 (toUnit Y ≫ f) x = 0 := by
  rw [← pO1_comp, pO1_unit_eq_zero (pO1 f x), map_zero]

theorem primO1_of_axesO1 {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (h : AxesVanishingStructureSheafDegOne A) : StructureSheafH1Primitive A := by
  intro x
  rw [← sub_eq_zero, sub_add_eq_sub_sub]
  apply h
  · rw [map_sub, map_sub, pO1_comp, pO1_comp, pO1_comp, lift_comp_one_right, lift_fst, lift_snd,
      pO1_toUnit_comp, pO1_id]
    simp
  · rw [map_sub, map_sub, pO1_comp, pO1_comp, pO1_comp, lift_comp_one_left, lift_fst, lift_snd,
      pO1_toUnit_comp, pO1_id]
    simp

theorem cup_add_cup_swap {R : Type} [CommRing R] {C : Type*} [Category C] (F : C ⥤ CommAlgCat.{0} R)
    (a b : CatCoh.H1 F) : cup F a b + cup F b a = 0 := by
  obtain ⟨a, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F a
  obtain ⟨b, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F b
  rw [GlobalTheory.CatCoh.cup_mk, GlobalTheory.CatCoh.cup_mk, ← map_add]
  refine GlobalTheory.CatCoh.H2.mk_eq_zero.2 ⟨fun T T' φ ↦ -(a.1 T T' φ * b.1 T T' φ), ?_⟩
  funext T T' T'' φ ψ
  simp only [GlobalTheory.CatCoh.d1_apply, Submodule.coe_add, Pi.add_apply, GlobalTheory.CatCoh.cupZ_apply, GlobalTheory.CatCoh.Z1.comp a,
    GlobalTheory.CatCoh.Z1.comp b, map_mul, map_neg]
  ring

theorem cup_self_eq_zero_of_prim {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (hP : StructureSheafH1Primitive A)
    (hN : NoPrimitiveStructureSheafH2 A) (x : HO1 A.hom) : cup _ x x = 0 := by
  have key : ∀ f : A ⊗ A ⟶ A, structureSheafH2Pullback f (cup _ x x) = cup _ (pO1 f x) (pO1 f x) := fun f ↦
    ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.1 _ _ _ _ _ _ _ _ (ovw f)).1 x x
  apply hN
  rw [key, key, key, hP x]
  simp only [map_add, LinearMap.add_apply]
  have := cup_add_cup_swap (OAff (A ⊗ A).hom) (pO1 (fst A A) x) (pO1 (snd A A) x)
  linear_combination (norm := module) this

theorem cup_self_eq_zero_of_isAbelianScheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R))
    [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ x : HO1 A.hom, cup _ x x = 0 := by
  intro R _ _ A _ g hA hg x
  exact cup_self_eq_zero_of_prim A (primO1_of_axesO1 A (GlobalTheory.T.axes_vanishing_noetherian_abelian R A g hA hg)) (GlobalTheory.T.abelian_scheme_no_primitive_O2 R A g hA hg) x

end GlobalTheory.AbCoh
