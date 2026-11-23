import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupVanishingAntisymmetricCrossStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyInclusionTensorInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossProductKernelQuotientVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeOfSymmetricTensorZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorSquareVectorBundleRankStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveOfSurjectiveSameRankStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.WedgeOf

theorem wedgeT_surjective (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] :
    Function.Surjective (wedgeT (R := R) V) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← exteriorPower.ιMulti_span (R := R) (n := 2) (M := V),
    Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  refine ⟨v 0 ⊗ₜ v 1, ?_⟩
  rw [wedgeT_tmul]
  congr 1
  funext i; fin_cases i <;> rfl

theorem wedgeOf_of_low : LowSt → WedgeOfSt := by
  intro hL R _ P _ _ F g hH hV hBC hV2 hspan
  have : Finite Pᵒᵖ := Finite.of_injective unop unop_injective
  have hV' := hV
  obtain ⟨hf, hp, -⟩ := hV'
  have hκ : Function.Surjective (TensorProduct.lift (cup F)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨x.1 ⊗ₜ x.2, rfl⟩
  have hinj : Function.Injective (TensorProduct.map (iotaQ F) (iotaQ F)) := by
    have e : TensorProduct.map (iotaQ F) (iotaQ F) =
        ((iotaQ F).lTensor (QC F)) ∘ₗ ((iotaQ F).rTensor (H1 F)) := by
      rw [LinearMap.lTensor_comp_rTensor]
    rw [e, LinearMap.coe_comp]
    exact (GlobalTheory.T.first_cohomology_inclusion_tensor_injective R _ F hBC (QC F)).comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ (iotaQ_injective F))
  have hker : LinearMap.ker (TensorProduct.lift (cup F)) ≤ LinearMap.ker (wedgeT (R := R) (H1 F)) := by
    intro t ht
    have h1 := GlobalTheory.T.cup_vanishing_antisymmetric_cross hL R _ F hH t ht
    have h2 := GlobalTheory.T.cross_product_kernel_quotient_vanishing R _ F _ h1
    have h3 := hinj (h2.trans (map_zero _).symm)
    exact GlobalTheory.T.wedge_of_symmetric_tensor_zero R _ t h3
  let s : H2 F →ₗ[R] ⋀[R]^2 (H1 F) :=
    (LinearMap.ker (TensorProduct.lift (cup F))).liftQ (wedgeT (R := R) (H1 F)) hker ∘ₗ
      (LinearMap.quotKerEquivOfSurjective _ hκ).symm.toLinearMap
  have hs : ∀ t, s (TensorProduct.lift (cup F) t) = wedgeT (R := R) (H1 F) t := by
    intro t
    have : (LinearMap.quotKerEquivOfSurjective _ hκ).symm (TensorProduct.lift (cup F) t) =
        Submodule.Quotient.mk t := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [s, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  have hsurj : Function.Surjective s := fun y ↦ by
    obtain ⟨t, rfl⟩ := wedgeT_surjective R (H1 F) y
    exact ⟨_, hs t⟩
  have hb := GlobalTheory.T.bijective_of_surjective_same_rank R _ _ _ hV2 (GlobalTheory.T.exterior_square_vector_bundle_rank R _ g hV) s hsurj
  refine ⟨(LinearEquiv.ofBijective s hb).symm, fun a b ↦ ?_⟩
  rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply]
  have := hs (a ⊗ₜ b)
  rw [wedgeT_tmul] at this
  exact this.symm

end GlobalTheory.CompanionTheory.WedgeOf
