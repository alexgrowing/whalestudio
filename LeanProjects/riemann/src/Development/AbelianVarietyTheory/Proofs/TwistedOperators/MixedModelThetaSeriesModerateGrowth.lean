import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRestrictedHeisenbergWeilTranslateAtZerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelThetaTermsSummableHeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrowStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedSeriesGrowth

theorem mixed_series_growth : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ A : ℕ, ∀ f, IsThetaFunO ψ V W f → ∃ c : ℝ, ∀ (g : GA D V) (h : GA D W), (∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, Continuous fun p : GA D V × GA D W => res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω p f)) 0) ∧ ∑' y : Matrix (Fin W.rank) (Fin r) D.host.E, ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω (g, h) f)) 0‖ₑ ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A) := by
  intro D V V' W r C C' B hs h1 h2 h3 ψ χS χT ω hω μ 𝓨 hμ
  obtain ⟨⟨θ, hθ⟩, -, -⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  obtain ⟨A₁, d, hF⟩ := GlobalTheory.T.mixedModelThetaTerms_summable_heightBound D V V' W r C C' B hs h1 h2 h3 ψ hω.std θ hθ μ 𝓨 hμ
  obtain ⟨A₂, hS⟩ := GlobalTheory.T.heisenbergWords_weilOperator_supNorm_polynomialGrowth D ψ V W χS χT ω hω θ hθ d
  refine ⟨A₁ + A₂, fun f hf => ?_⟩
  obtain ⟨U, hU, hl⟩ := hf.level
  obtain ⟨K, hK⟩ := hF U hU
  obtain ⟨c, hc⟩ := hS f hf
  refine ⟨max K 0 * max c 0, fun g h => ⟨fun y => GlobalTheory.T.continuous_restrictedHeisenbergWeilTranslate_at_zero D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ f hf _, ?_⟩⟩
  have hH : 0 ≤ GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h :=
    mul_nonneg (GlobalTheory.Grow.height_pos V g).le (GlobalTheory.Grow.height_pos W h).le
  refine (hK g h (ω (g, h) f) (hω.om_pres _ f hf) (fun u hu h0 => ?_)).trans ?_
  · rw [← hω.om_heis g h u f hf, hl u hu h0]
  · refine (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left K 0) (pow_nonneg hH _)))
      ((hc g h).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left c 0)
        (pow_nonneg hH _))))).trans_eq ?_
    rw [← ENNReal.ofReal_mul (mul_nonneg (le_max_right K 0) (pow_nonneg hH _)), pow_add]
    congr 1; ring

end GlobalTheory.MixedSeriesGrowth

end
