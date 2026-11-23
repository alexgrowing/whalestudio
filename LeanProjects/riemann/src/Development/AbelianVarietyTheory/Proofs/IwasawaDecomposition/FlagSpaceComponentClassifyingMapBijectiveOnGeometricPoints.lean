import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyFlagRefinementBundleOfGoodModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagRefinementBundleComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenFrameBasePointLiftsUniqueFlagSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentBaseMapOfFunctionFieldsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFullFlagFamilyLieCompatibleGradedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagFramesFlagComponentPullbackBaseFramesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionFieldMapFullFlagGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleFunctionFieldMapDominatesLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionFieldIntegralModelExistsIsHomOfMapLocalRStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBijectiveFieldPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBearsFlagsOfGenericStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.ClsMap

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (Y' : Var F) (φ' : X.Fn →ₐ[F] Y'.Fn) (f' : Y'.X ⟶ X.X) (S' : Fr (ratOf Y') Dw.mult Dw.mult), Refines Eb S' φ' f' → ∃ h : C.Y.X ⟶ Y'.X, h ≫ f' = f ∧ ∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ C.Y.X => p ≫ h) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j hjo hj f hπ f₀ Eb A₀ hT hL Y' φ' f' S' hR'

  obtain ⟨φ, hφ⟩ := GlobalTheory.T.flagSpaceComponent_baseMap_of_functionFields E H Dw l Xo c O β Z F e C X j hjo hj f hπ hL
  have hgen : genericPt C.Y ≫ f = spMap (φ : X.Fn →+* C.Y.Fn) ≫ genericPt X := hφ
  have hx : genericPt C.Y ≫ C.π ≫ genι Z = spMap (φ : X.Fn →+* C.Y.Fn) ≫ genericPt X ≫ j ≫ genι Z := by
    rw [← hπ, Category.assoc, ← Category.assoc, hgen, Category.assoc]
  have hc : constF e C.Y = (φ : X.Fn →+* C.Y.Fn).comp (constF e X) :=
    RingHom.ext fun a => (φ.commutes _).symm
  have hst₀ : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f₀ inferInstance
  obtain ⟨⟨M, hM, -⟩, hMu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f₀ C.Y.Fn (constF e C.Y)
    (genericPt C.Y ≫ C.π ≫ genι Z) (φ : X.Fn →+* C.Y.Fn) inferInstance hst₀ hx hc).1 C.f0
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hT.1
  have hA₀φ : ∀ τ, ((A₀.map φ) τ).det ≠ 0 := fun τ =>
    (Mat.det_map A₀ (φ : X.Fn →+* C.Y.Fn) τ).trans_ne ((map_ne_zero _).2 (hA₀d τ))
  set A₁ : Mat Dw.mult C.Y.Fn := M * A₀.map φ with hA₁
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := fun τ => by
    rw [hA₁, Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hMu M hM τ).ne_zero (hA₀φ τ)
  have hC : f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) := by
    rw [hA₁, mul_assoc, Mat.mul_inv hA₀φ, mul_one]; exact hM
  obtain ⟨E', hT', -⟩ := GlobalTheory.T.exists_fullFlagFamily_lieCompatible_graded E H Dw l Xo c O β Z F e C A₁ hA₁d
  have hsub := GlobalTheory.T.fullFlagFrames_flagComponent_pullback_baseFrames E H Dw l Xo c O β Z F e C X j f hπ f₀ Eb A₀ hT φ hφ E' A₁ hT' hC
  have R₁ : Reps Eb E' φ f := ⟨hφ, hsub,
    GlobalTheory.T.flagSpace_unique_lift_any_field E H Dw l Xo c O β Z F e C X j hjo hj f hπ f₀ Eb A₀ hT hL φ hφ E' A₁ hT' hC hsub⟩
  have R₂ : Reps Eb S' φ' f' := hR'.reps

  obtain ⟨ψ, hψ, hG⟩ := GlobalTheory.T.exists_functionField_map_fullFlag_generic_point F (E →+* ℂ) Dw.mult X C.Y Y' Eb E' φ f S' φ' f' R₁ R₂
  obtain ⟨h, hh⟩ := GlobalTheory.T.functionFieldIntegralModel_exists_isHom_of_map_localRing F Y'.Fn (ratOf Y') C.Y.Fn (ratOf C.Y) ψ
    (GlobalTheory.T.fullFlagBundle_functionFieldMap_dominates_localRings F (E →+* ℂ) Dw.mult X C.Y Y' Eb E' φ f S' φ' f' R₁ R₂ ψ hψ hG)
  have hf : h ≫ f' = f := by
    have h1 := R₂.1.comp hh
    rw [hψ] at h1
    exact h1.unique hφ
  refine ⟨h, hf, fun K _ _ => GlobalTheory.T.fullFlagBundleMorphism_bijective_fieldPoints F (E →+* ℂ) Dw.mult X C.Y Y' Eb E' φ f S' φ' f' R₁ R₂ h hf
    (GlobalTheory.T.fullFlagBundleMorphism_bearsFlags_of_generic F (E →+* ℂ) Dw.mult X C.Y Y' Eb E' φ f S' φ' f' R₁ R₂ ψ hψ hG h hh) K⟩

end GlobalTheory.ShFam.ClsMap
