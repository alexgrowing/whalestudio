import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyMulLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierConstantAtZeroDifferentiableOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierConstantAtZeroZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperHalfPlaneProductProdImRpowContDiffOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdImIteratedWirtingerDerivWordDifferentiableOnStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo

namespace BZeroGood

theorem card_emb_totReal (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (Emb F) = Module.finrank ℚ F := by
  rw [← Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun τ : F →+* ℝ => Complex.ofRealHom.comp τ) ⟨fun τ τ' h => ?_, fun φ => ?_⟩
  · ext x
    exact Complex.ofReal_injective (RingHom.congr_fun h x)
  · exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, RingHom.ext fun x =>
      (IsTotallyReal.complexEmbedding_isReal φ).coe_embedding_apply x⟩

theorem halfPlane_mem_nhds_zero : halfPlane ∈ nhds (0 : ℂ) := by
  refine (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_
  show (-1 / 2 : ℝ) < (0 : ℂ).re
  norm_num

theorem _root_.GlobalTheory.HeckeTwo.bZero_isGood (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (hf : 2 ≤ Module.finrank ℚ F)
    (𝔞 𝔟 : Frac F) (Zb R : ℂ → ℂ) (hR : Differentiable ℂ R) (hZ : ∀ s : ℂ, s ≠ 1 → Zb s = R s / (s - 1)) :
    IsGood (bZero Zb 𝔞 𝔟) := by
  set f := Fintype.card (Emb F) with hfdef
  have hf2 : 2 ≤ f := by rw [hfdef, card_emb_totReal F]; exact hf
  set E : ℂ → ℂ := fun σ => if σ = 0 then 0 else
    kFac F σ * (omegaFactor 𝔞 : ℂ) * ((nrm 𝔟 : ℝ) : ℂ) ^ (-1 - 2 * σ) * Zb (1 + 2 * σ) * cConst σ ^ f with hE
  set G : ℂ → ℂ := fun σ =>
    kFac F σ * (omegaFactor 𝔞 : ℂ) * ((nrm 𝔟 : ℝ) : ℂ) ^ (-1 - 2 * σ) * (R (1 + 2 * σ) / 2) *
      dslope cConst 0 σ * cConst σ ^ (f - 1) with hG
  have hEG : E = G := by
    funext σ
    simp only [hE, hG]
    split_ifs with h0
    · subst h0
      rw [GlobalTheory.T.heckePhiFourierConstantAtZero_zero, zero_pow (by omega), mul_zero]
    · rw [dslope_of_ne _ h0, slope_def_field, GlobalTheory.T.heckePhiFourierConstantAtZero_zero, hZ _ (by
          intro h; apply h0; linear_combination h / 2)]
      have hf1 : f = (f - 1) + 1 := by omega
      rw [hf1, pow_succ]
      simp only [Nat.add_sub_cancel]
      field_simp
      ring
  have hGd : DifferentiableOn ℂ G halfPlane := by
    intro σ hσ
    have hσ' : -1 - 2 * σ ≠ 0 := by
      intro h
      have : σ.re = -1 / 2 := by
        have := congrArg Complex.re h
        simp at this
        linarith
      simp only [halfPlane, Set.mem_setOf_eq] at hσ
      linarith
    have h1 : DifferentiableAt ℂ (fun σ : ℂ => ((nrm 𝔟 : ℝ) : ℂ) ^ (-1 - 2 * σ)) σ :=
      DifferentiableAt.const_cpow ((differentiableAt_const _).sub (differentiableAt_id.const_mul _)) (Or.inr hσ')
    have h2 : DifferentiableAt ℂ (fun σ : ℂ => R (1 + 2 * σ)) σ :=
      (hR _).comp σ ((differentiableAt_const _).add (differentiableAt_id.const_mul _))
    have h3 : DifferentiableWithinAt ℂ (dslope cConst 0) halfPlane σ :=
      ((differentiableOn_dslope halfPlane_mem_nhds_zero).2 GlobalTheory.T.heckePhiFourierConstantAtZero_differentiableOn) σ hσ
    have h4 : DifferentiableWithinAt ℂ cConst halfPlane σ := GlobalTheory.T.heckePhiFourierConstantAtZero_differentiableOn σ hσ
    exact ((((kFac_differentiable σ).differentiableWithinAt.mul (differentiableWithinAt_const _)).mul
      h1.differentiableWithinAt).mul (h2.differentiableWithinAt.div_const _)).mul h3 |>.mul (h4.pow _)
  have hB : bZero Zb 𝔞 𝔟 = fun σ z => E σ * ∏ τ : Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
    funext σ z
    simp only [bZero, hE]
    split_ifs
    · simp
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      ring
  rw [hB]
  exact GlobalTheory.HeckeTwoMul.isGood_mul F E _ (hEG ▸ hGd) ⟨fun σ _ => GlobalTheory.T.upperHalfPlaneProduct_prod_im_rpow_contDiffOn F σ, fun w z hz => GlobalTheory.T.prodIm_iteratedWirtingerDerivWord_differentiableOn F w z hz⟩

end BZeroGood

end GlobalTheory.HeckeTwo
