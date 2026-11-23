import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFDomS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFFormIdS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormDone
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENFMainS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibMain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopPtw

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def flCutS (k r : ℕ) (n : ℕ) (g : B.Mat k r) : ℂ :=
  ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)

theorem domination_measurability_holds : NFDomMeas := by
  intro Cb
  obtain ⟨Cc, hFL⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  obtain ⟨hχ, hInD, hfck, hfcc, hA, -⟩ := hH
  have hck : B.CkOn ⊤ (B.GV P.k P.r) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) := by
    rw [fpm_id]; exact ckOn_Gpow_smul _ _ p₀ hfck
  obtain ⟨hcpt, hlim⟩ := hFL Wp Wq P p (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) χ ε
    (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) N (flCutS P.k P.r) hInD hχ hε hck (inCC_fpm_id p p₀ hfcc) hA
    (fun n g => rfl)
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n => topD p (fun g => flCutS P.k P.r n g •
      D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε g) w)
    (fun n => top_domination_measurable_compact Wp Wq P p _ w Cb hInD (hcpt n) hw.1) (ae_of_all _ fun c => ?_)
  have h := hlim (P.r + 1) w hw.1 hN (TBB.bigPt P.r c) (TBB.bigPt P.r c)
  unfold topD TBB.Ew TBB.NP
  exact (Complex.continuous_re.tendsto _).comp (h.const_mul _)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_main6 (hA : P5.ThmPActual) (hT : NFTieHatS) (hH : NFHatProdKBS) (hJC : NFJCutFF) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      B.JF p.T.base f ∈ FFKB p →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn
        (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) Y K N) →
      LimBd p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by

  have hTM : TopDMeasCpt := Formalism.FourierDecayAlt.P.CutBP.top_domination_measurable_compact

  have hCore : NFCoreNS := Formalism.FourierDecayAlt.P.CutBP.nFCoreNS_of_cut Formalism.FourierDecayAlt.P.CutBP.leibniz_vector_estimate_holds hT hH Formalism.FourierDecayAlt.P.CutBP.trace_norm_bound_constant_one Formalism.FourierDecayAlt.P.CutBP.operator_multiplication_admissible
  have hDP : NFDomPtwS := Formalism.FourierDecayAlt.P.CutBP.nfDomPtwS_of_cut Formalism.FourierDecayAlt.P.CutBP.unfolding_top_term_holds Formalism.FourierDecayAlt.P.CutBP.vector_multiplication_holds Formalism.FourierDecayAlt.P.CutBP.truncated_supremum_bound_holds
    Formalism.FourierDecayAlt.P.CutBP.leibniz_vector_estimate_holds hCore Formalism.FourierDecayAlt.P.CutBP.empty_operator_list_holds
  have hApx : NFApxDomAllS := Formalism.FourierDecayAlt.P.CutBP.nfApxDomAllS_of_cut Formalism.FourierDecayAlt.P.CutBP.domination_at_zero_holds hDP Formalism.FourierDecayAlt.P.CutBP.dominated_L2_truncation_bound_holds
  have hForm : NFTopFormAllS := Formalism.FourierDecayAlt.P.CutBP.nFTopFormAllS_of hTM hApx
  have hDom : NFTopDomAllS := Formalism.FourierDecayAlt.P.CutBP.nfTopDomAllS_of_cut Formalism.FourierDecayAlt.P.CutBP.domination_at_zero_holds hDP Formalism.FourierDecayAlt.P.CutBP.dominated_L2_operator_bound_holds domination_measurability_holds

  have hPQ : NFPolQuadAllS := Formalism.FourierDecayAlt.P.CutBP.nfPolQuadAllS_of hTM hApx
  have hPF : NFPolFormAllS := Formalism.FourierDecayAlt.P.CutBP.nfPolFormAllS_of hPQ Formalism.FourierDecayAlt.P.CutBP.pairing_middle_all_levels_holds Formalism.FourierDecayAlt.P.CutBP.top_middle_all_levels_holds
  have hId : NFTopIdAllS := Formalism.FourierDecayAlt.P.CutBP.nfTopIdAllS_of hA hDom hPF Formalism.FourierDecayAlt.P.CutBP.pairing_pointwise_all_levels_holds Formalism.FourierDecayAlt.P.CutBP.beta_limit_all_levels_holds
  exact Formalism.FourierDecayAlt.P.CutBP.thmBpAt_main5 hA hForm Formalism.FourierDecayAlt.P.CutBP.top_pointwise_all_levels_holds hDom hId hJC Cb C₃ CΛ C₀ hC₃ hCΛ hC₀

end

end Formalism.FourierDecayAlt.P.CutBP
