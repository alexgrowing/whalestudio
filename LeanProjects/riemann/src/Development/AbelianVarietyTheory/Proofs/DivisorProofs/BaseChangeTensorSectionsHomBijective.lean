import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensHomTmul
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BC

theorem isPushout_sec (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (U : X₀.affineOpens) :
    IsPushout (secMap s₀ U.1) (CommRingCat.ofHom (algebraMap R₀ R₁)) (pr.appLE U.1 (pr ⁻¹ᵁ U.1) le_rfl)
      (secMap s₁ (pr ⁻¹ᵁ U.1)) := by
  have po := (isIso_pushoutSection_iff hp (US := ⊤) (UT := ⊤) (UX := U.1) (UY := pr ⁻¹ᵁ U.1) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen hp _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) U.2)
  refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, ← Iso.inv_comp_eq]
    rfl
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp
  · rw [Iso.refl_hom, Category.comp_id, ← Iso.inv_comp_eq]
    rfl

theorem tensHom_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (U : X₀.affineOpens) (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)), Function.Bijective (GlobalTheory.Obs.BC.tensHom hp.w U hU) := by
  intro R₀ R₁ _ _ _ X₀ X₁ s₀ s₁ pr hp U hU
  letI : Algebra R₀ (Sec s₁ (pr ⁻¹ᵁ U.1)) := ((algebraMap R₁ _).comp (algebraMap R₀ R₁)).toAlgebra
  haveI : IsScalarTower R₀ R₁ (Sec s₁ (pr ⁻¹ᵁ U.1)) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1)) := (prSec hp.w U hU).toAlgebra
  haveI : IsScalarTower R₀ (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1)) := IsScalarTower.of_algebraMap_eq fun r ↦
    ((semiHom_secPull hp.w (⟨(⟨pr ⁻¹ᵁ U.1, hU⟩, U), le_rfl⟩ : Pair pr)).map_algebraMap r).symm
  have hpo : Algebra.IsPushout R₀ R₁ (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1)) :=
    CommRingCat.isPushout_iff_isPushout.mp (isPushout_sec R₀ R₁ X₀ X₁ s₀ s₁ pr hp U).flip
  have e : ∀ x, tensHom hp.w U hU x = Algebra.IsPushout.equiv R₀ R₁ (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1)) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul r b => rw [tensHom_tmul, Algebra.IsPushout.equiv_tmul]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have : ⇑(tensHom hp.w U hU) = ⇑(Algebra.IsPushout.equiv R₀ R₁ (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1))) := funext e
  rw [this]
  exact (Algebra.IsPushout.equiv R₀ R₁ (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1))).bijective

end GlobalTheory.Obs.BC
