import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianInterpolation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterpolatedMetricCurvatureBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMetricGradientFormBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutWeightContDiffOnMemIcc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterpolatedMetricPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffInterpolationAgreesFarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffInterpolationUniformLimitStatement

open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.InterpCurv

theorem interpCurvBound : InterpCurvBound := by
  intro Cμ C₀ C₂ C₃ CP κ χ hκ hχ
  obtain ⟨K, hK⟩ := GlobalTheory.T.log_metric_gradient_form_bound Cμ CP κ χ hκ hχ
  refine ⟨2 * (|C₀| + |C₃| + 2 * C₂ ^ 2 + 4 * |K| + 3 * K ^ 2), ?_⟩
  intro ι n _ _ _ U H₀ H r G hD
  have hr1 : ∀ z ∈ U, 1 < r z := fun z hz =>
    (Real.one_lt_exp_iff.2 one_pos).trans_le (hD.exp_le z hz)
  have hW : ∀ s, IsWeight χ κ r s →
      ContDiffOn ℝ ∞ s U ∧ (∀ z ∈ U, s z ∈ Icc (0 : ℝ) 1) ∧ (0 ≤ Cμ → WeightBound K Cμ U r s G) := by
    rintro s (⟨c, hc, rfl⟩ | ⟨t, ht, R, hR, rfl⟩)
    · exact ⟨contDiffOn_const, fun _ _ => hc, fun _ => weightBound_const K Cμ U r G hc⟩
    · obtain ⟨h1, h2⟩ := GlobalTheory.cutWeight_contDiffOn_mem_Icc hχ κ hR hD.smooth_r hD.exp_le
      refine ⟨contDiffOn_const.mul h1, fun z hz => ⟨mul_nonneg ht.1 (h2 z hz).1, ?_⟩,
        fun hC => hK ι U r G hC hD.pos₀.1 hD.smooth_r hD.exp_le hD.posSemidef_G hD.grad_le hD.ddc_log_le
          t ht R hR⟩
      exact mul_le_one₀ ht.2 (h2 z hz).1 (h2 z hz).2
  refine ⟨fun s hs => ?_, fun t ht R hR => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hW s hs
    obtain ⟨b1, b2, b3⟩ := GlobalTheory.T.interpolated_metric_positive hD.pos₀ hD.pos hD.exp_le h1 h2 hD.comparable
    exact ⟨b1, GlobalTheory.T.interpolated_metric_curvature_bound hD.pos₀ hD.pos hr1 h1 hD.posSemidef_G hD.comparable hD.conn_le
      hD.curv_le hD.curv₀_le h3, b2, b3⟩
  · obtain ⟨h1, h2, -⟩ := hW _ (Or.inr ⟨t, ht, R, hR, rfl⟩)
    exact GlobalTheory.T.cutoff_interpolation_agrees_far hχ hR hD.exp_le
      (GlobalTheory.T.interpolated_metric_positive hD.pos₀ hD.pos hD.exp_le h1 h2 hD.comparable).1
  · exact GlobalTheory.T.cutoff_interpolation_uniform_limit hχ hκ hD.pos₀ hD.pos hD.smooth_r hD.exp_le hD.comparable

end GlobalTheory.InterpCurv
