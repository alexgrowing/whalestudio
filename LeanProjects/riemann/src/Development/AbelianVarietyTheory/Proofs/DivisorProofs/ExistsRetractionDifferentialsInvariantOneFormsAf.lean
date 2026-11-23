import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormEqZeroOfAffineCoverRestrictionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorKaehlerEqZeroOfDerivationsVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLawTranslateDerivationInvariantFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInvariantOneFormsAffineOpenAbelianSchemeEqToStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.InvForm

namespace GlobalTheory.InvFormRetract

theorem dVal_smul {R B D : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing D] [Algebra R D] (φ : B →ₐ[R] DualNumber D) (b : B) (x : Ω[B⁄R]) : dVal φ (b • x) = redHom φ b * dVal φ x := by
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  unfold dVal
  simp only [LinearMap.restrictScalars_apply, LinearMap.map_smul]
  rfl

theorem injective_baseChange {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (hab : IsAbelianScheme A) (U : AffOp A.left) :
    Function.Injective (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype)) := by
  haveI : Smooth A.hom := hab.smooth
  haveI : IsProper A.hom := hab.proper
  haveI : CompactSpace A.left := ⟨by simpa using QuasiCompact.isCompact_preimage (f := A.hom) Set.univ isOpen_univ isCompact_univ⟩
  haveI : Algebra.Smooth R (Sec A.hom U.unop.1) := smooth_sec_affine A.hom U.unop
  haveI : Module.Flat R (Sec A.hom U.unop.1) := Algebra.Smooth.flat R _
  obtain ⟨n, V, hV⟩ := GlobalTheory.T.exists_finite_affineCover_globalForm_eq_zero_of_restrictions R A.left A.hom inferInstance
  let f : ∀ k, InvForm A →ₗ[R] Ω[Sec A.hom (V k).unop.1⁄R] := fun k => evForm A.hom (V k) ∘ₗ (InvForm A).subtype
  let F : InvForm A →ₗ[R] ((k : Fin n) → Ω[Sec A.hom (V k).unop.1⁄R]) := LinearMap.pi f
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (hV w.1 fun k => congrFun hw k)
  have hFB : Function.Injective (LinearMap.lTensor (Sec A.hom U.unop.1) F) :=
    Module.Flat.lTensor_preserves_injective_linearMap F hF
  have hk : ∀ (k : Fin n) (z : Sec A.hom U.unop.1 ⊗[R] InvForm A), TensorProduct.piRight R R (Sec A.hom U.unop.1) (fun k : Fin n => Ω[Sec A.hom (V k).unop.1⁄R])
      (LinearMap.lTensor (Sec A.hom U.unop.1) F z) k = LinearMap.lTensor (Sec A.hom U.unop.1) (f k) z := by
    intro k z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b w => simp [F]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  apply hFB
  rw [map_zero]
  apply (TensorProduct.piRight R R (Sec A.hom U.unop.1) (fun k : Fin n => Ω[Sec A.hom (V k).unop.1⁄R])).injective
  rw [map_zero]
  funext k
  rw [hk, Pi.zero_apply]
  haveI : Algebra.Smooth R (Sec A.hom (V k).unop.1) := smooth_sec_affine A.hom (V k).unop
  refine GlobalTheory.T.eq_zero_of_liftBaseChange_derivations_eq_zero R (Sec A.hom U.unop.1) _ inferInstance _ (fun θ hθ => ?_)
  obtain ⟨ψ, hfst, hψ⟩ := GlobalTheory.T.exists_groupLawTranslate_derivation_invariantForms R A U (V k) θ hθ
  have key : ∀ y, LinearMap.liftBaseChange (Sec A.hom U.unop.1) θ (LinearMap.lTensor (Sec A.hom U.unop.1) (f k) y) =
      dVal ψ (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b w =>
      rw [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, dVal_smul]
      have h1 : redHom ψ b = b ⊗ₜ 1 := hfst b
      rw [h1, Algebra.smul_def]
      simp only [f, LinearMap.comp_apply, Submodule.subtype_apply, hψ]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [key, hz, map_zero]

theorem retract : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left, ∃ r : Ω[Sec A.hom U.unop.1⁄R] →ₗ[Sec A.hom U.unop.1] (Sec A.hom U.unop.1 ⊗[R] GlobalTheory.InvForm.InvForm A), ∀ w : GlobalTheory.InvForm.InvForm A, r (evForm A.hom U w.1) = 1 ⊗ₜ w := by
  intro R _ A _ g hab hdim U
  have hsurj : Function.Surjective (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← GlobalTheory.T.span_invariantOneForms_affineOpen_abelianScheme_eq_top R A g hab hdim U, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact ⟨1 ⊗ₜ w, by simp⟩
  let e := LinearEquiv.ofBijective _ ⟨injective_baseChange A hab U, hsurj⟩
  refine ⟨e.symm.toLinearMap, fun w => ?_⟩
  apply e.injective
  rw [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
  change _ = LinearMap.liftBaseChange _ _ (1 ⊗ₜ w)
  rw [LinearMap.liftBaseChange_tmul, one_smul]
  rfl

end GlobalTheory.InvFormRetract
