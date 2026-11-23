import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisOApplyZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionInvariantRationalLeviScaling
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPa
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestriction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviGLRes

local infixl:70 " ⬝ " => HMul.hMul

variable {D : D7}

theorem covolOne_integral_mul_right {m n : ℕ} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (hμ : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓕) (M M' : Mx D n n) (hM'M : M' * M = 1) (hMM' : M * M' = 1)
    (hM : M ∈ GlobalTheory.MixModel.ratMx D n n) (hM' : M' ∈ GlobalTheory.MixModel.ratMx D n n) (φ : Mx D m n → ℂ)
    (hφ : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, φ (γ + a) = φ a) :
    ∫ a in 𝓕, φ (a ⬝ M) ∂μ = ∫ a in 𝓕, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  let e : Mx D m n ≃+ Mx D m n :=
    { toFun := fun a => a ⬝ M
      invFun := fun a => a ⬝ M'
      left_inv := fun a => by simp only [Matrix.mul_assoc, hMM', Matrix.mul_one]
      right_inv := fun a => by simp only [Matrix.mul_assoc, hM'M, Matrix.mul_one]
      map_add' := fun a b => Matrix.add_mul _ _ _ }
  have he : Continuous e := continuous_id.matrix_mul continuous_const
  have he' : Continuous e.symm := continuous_id.matrix_mul continuous_const
  have hr : ∀ x, e x ∈ GlobalTheory.MixModel.ratMx D m n ↔ x ∈ GlobalTheory.MixModel.ratMx D m n := fun x =>
    ⟨fun h => by
      have h2 := GlobalTheory.MixModel.ratMx_mul h hM'
      have h3 : e x ⬝ M' = x := e.symm_apply_apply x
      rwa [h3] at h2,
     fun h => GlobalTheory.MixModel.ratMx_mul h hM⟩
  obtain ⟨h1, hemb⟩ := GlobalTheory.Unf.ParCont.isCovolOne_map hμ e he he' hr
  rw [← GlobalTheory.MixModel.covolOne_integral_eq hμ h1 φ hφ, hemb.setIntegral_map, Set.preimage_image_eq _ e.injective]
  rfl

end GlobalTheory.LeviGLRes

namespace GlobalTheory.LeviGLRes

local infixl:70 " ⬝ " => HMul.hMul

theorem res_levi_GL : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (d : GlobalTheory.MixModel.HypDec V V' r), d.e = C → d.i₀ = B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (a : GL (Fin r) D.host.E) (f : WO V W → ℂ), IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (d.levi (Matrix.GeneralLinearGroup.map (incA D) a), 1) f) = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs d hC hB ψ χS χT ω hω μ 𝓨 hcov a f hf
  subst hC hB
  set A : GL (Fin r) (AE D) := Matrix.GeneralLinearGroup.map (incA D) a with hA
  have hA1 : A.1 = GlobalTheory.MixModel.rat a.1 := rfl
  have hAi : (A⁻¹).1 = GlobalTheory.MixModel.rat (a⁻¹).1 := rfl
  have hmem : d.levi A ∈ GQ V :=
    d.levi_mem_GQ (by rw [hA1]; exact GlobalTheory.MixModel.rat_mem _) (by rw [hAi]; exact GlobalTheory.MixModel.rat_mem _)
  have hsub : ∀ w : WO V W, ω (d.levi A, 1) f w = f (w ⬝ Formalism.L2.Theta.mt V (d.levi A)) := fun w => by
    have h := GlobalTheory.WeilRat.om_rat_actO D ψ hω.std V W χS χT ω hω _ hmem 1 (one_mem _) f hf
      (w ⬝ Formalism.L2.Theta.mt V (d.levi A))
    rwa [GlobalTheory.LeviRes.actO_mul_mt] at h
  set M : Mx D r r := GlobalTheory.MixModel.adj (A⁻¹).1 with hMdef
  set M' : Mx D r r := GlobalTheory.MixModel.adj A.1 with hM'def
  have hMM' : M * M' = 1 := by
    rw [hMdef, hM'def, ← GlobalTheory.MixModel.adj_mul, Units.mul_inv, GlobalTheory.MixModel.adj_one]
  have hM'M : M' * M = 1 := by
    rw [hMdef, hM'def, ← GlobalTheory.MixModel.adj_mul, Units.inv_mul, GlobalTheory.MixModel.adj_one]
  have hM : M ∈ GlobalTheory.MixModel.ratMx D r r := GlobalTheory.MixModel.ratMx_adj (by rw [hAi]; exact GlobalTheory.MixModel.rat_mem _)
  have hM' : M' ∈ GlobalTheory.MixModel.ratMx D r r := GlobalTheory.MixModel.ratMx_adj (by rw [hA1]; exact GlobalTheory.MixModel.rat_mem _)
  funext x
  have key : ∀ y : Mx D W.rank r,
      ω (d.levi A, 1) f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x) =
        f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e (y ⬝ M) + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x) := by
    intro y
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e y ⬝ Formalism.L2.Theta.mt V (d.levi A) =
        GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e (y ⬝ M) := by
      show (y ⬝ d.pY) ⬝ Formalism.L2.Theta.mt V (d.levi A) = (y ⬝ M) ⬝ d.pY
      rw [Matrix.mul_assoc, d.pY_levi, ← Matrix.mul_assoc]
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x ⬝ Formalism.L2.Theta.mt V (d.levi A) =
        GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x := by
      rw [GlobalTheory.Bridge.orthProjPartHomToHermitian_eq_wittDecompositionCore, GlobalTheory.MixModel.HypDec.matrixExtendByZero_apply, Matrix.mul_assoc, d.wittDecomp_projAnisotropic_levi]
    rw [hsub, Matrix.add_mul, e1, e2]
  show ∫ y in 𝓨, ω (d.levi A, 1) f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x) ∂μ =
    ∫ y in 𝓨, f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x) ∂μ
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  exact covolOne_integral_mul_right hcov M M' hM'M hMM' hM hM'
    (fun y => f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x))
    (GlobalTheory.LeviRes.periodic hs hf x)

end GlobalTheory.LeviGLRes
