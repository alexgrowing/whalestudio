import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NegMulCCancel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX.MkTopBump

theorem bump_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (f g : E → ℂ) (hf : Continuous f) (hg : Continuous g) (hf0 : f 0 = 1) (hg0 : g 0 = 1) :
    ∃ b : E → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ (∫ x, (b x : ℂ) * f x ∂μ) ≠ 0 ∧
      (∫ x, (b x : ℂ) * g x ∂μ) ≠ 0 := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 hf.continuousAt (1 / 2 : ℝ) (by norm_num)
  obtain ⟨δ', hδ', hδg⟩ := Metric.continuousAt_iff.1 hg.continuousAt (1 / 2 : ℝ) (by norm_num)
  have hm : 0 < min δ δ' := lt_min hδ hδ'
  let B : ContDiffBump (0 : E) := ⟨min δ δ' / 4, min δ δ' / 2, by positivity, by linarith⟩
  set b : E → ℝ := fun x => B x with hbdef
  have hbd : ContDiff ℝ ∞ b := B.contDiff
  have hbc : HasCompactSupport b := B.hasCompactSupport
  have hbnn : ∀ x, 0 ≤ b x := fun x => B.nonneg
  have hbcont : Continuous b := B.continuous
  have hbint : 0 < ∫ x, b x ∂μ := B.integral_pos
  have hbs : tsupport b ⊆ Metric.ball (0 : E) (min δ δ') := by
    rw [show tsupport b = Metric.closedBall (0 : E) (min δ δ' / 2) from B.tsupport_eq]
    exact Metric.closedBall_subset_ball (by linarith)
  have aux : ∀ h : E → ℂ, Continuous h →
      (∀ x, dist x 0 < min δ δ' → ‖h x - 1‖ < 1 / 2) → (∫ x, (b x : ℂ) * h x ∂μ) ≠ 0 := by
    intro h hh hs
    have hbC : Continuous (fun x => (b x : ℂ)) := Complex.continuous_ofReal.comp hbcont
    have hbcC : HasCompactSupport (fun x => (b x : ℂ)) := hbc.comp_left Complex.ofReal_zero
    have hi1 : Integrable (fun x => (b x : ℂ)) μ := hbC.integrable_of_hasCompactSupport hbcC
    have hi2 : Integrable (fun x => (b x : ℂ) * (h x - 1)) μ :=
      (hbC.mul (hh.sub continuous_const)).integrable_of_hasCompactSupport (hbcC.mul_right)
    have hi3 : Integrable (fun x => b x * (1 / 2 : ℝ)) μ :=
      (hbcont.integrable_of_hasCompactSupport hbc).mul_const _
    have split : (∫ x, (b x : ℂ) * h x ∂μ) = (∫ x, (b x : ℂ) ∂μ) + ∫ x, (b x : ℂ) * (h x - 1) ∂μ := by
      rw [← integral_add hi1 hi2]
      congr 1
      funext x
      ring
    have hbound : ‖∫ x, (b x : ℂ) * (h x - 1) ∂μ‖ ≤ ∫ x, b x * (1 / 2 : ℝ) ∂μ := by
      refine norm_integral_le_of_norm_le hi3 (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hbnn x)]
      by_cases hbx : b x = 0
      · rw [hbx]; simp
      · have hx : x ∈ Metric.ball (0 : E) (min δ δ') := hbs (subset_tsupport _ hbx)
        exact mul_le_mul_of_nonneg_left (hs x hx).le (hbnn x)
    have hreal : (∫ x, (b x : ℂ) ∂μ) = ((∫ x, b x ∂μ : ℝ) : ℂ) := integral_ofReal
    rw [integral_mul_const] at hbound
    intro h0
    rw [split, hreal] at h0
    have e1 : ((∫ x, b x ∂μ : ℝ) : ℂ) = -∫ x, (b x : ℂ) * (h x - 1) ∂μ := eq_neg_of_add_eq_zero_left h0
    have e2 : ‖((∫ x, b x ∂μ : ℝ) : ℂ)‖ = ‖∫ x, (b x : ℂ) * (h x - 1) ∂μ‖ := by rw [e1, norm_neg]
    rw [Complex.norm_real, Real.norm_of_nonneg hbint.le] at e2
    linarith
  refine ⟨b, hbd, hbc, aux f hf fun x hx => ?_, aux g hg fun x hx => ?_⟩
  · have := hδf (lt_of_lt_of_le hx (min_le_left _ _))
    rwa [hf0, dist_eq_norm] at this
  · have := hδg (lt_of_lt_of_le hx (min_le_right _ _))
    rwa [hg0, dist_eq_norm] at this

local instance bsS {p : ℕ} : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
local instance bsRC {k p ρ : ℕ} : BorelSpace (U.RC k p ρ) := Prod.borelSpace

theorem piHaar {n p : ℕ} : (volume : Measure (Fin n → Fin p → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ => volume)

theorem rcHaar {k p ρ : ℕ} : (volume : Measure (U.RC k p ρ)).IsAddHaarMeasure := by
  have := @piHaar (2 * ρ + k + 1) p
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure _ _

theorem bump_exists {k p ρ : ℕ} (z z' : Fin (2 * ρ + k + 1) → ℂ) (hz : inWb k ρ z) (hz' : inWb k ρ z') :
    ∃ b : U.RC k p ρ → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      (∫ x, (b x : ℂ) * psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ x) ∂(U.muRC k p ρ)) ≠ 0 ∧
      (∫ x, (b x : ℂ) * star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)) ∂(U.muRC k p ρ)) ≠ 0 := by
  have hc : Continuous (fun x : U.RC k p ρ => psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ x)) :=
    (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_cont _ _).comp (Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont p ρ)
  have hc' : Continuous (fun x : U.RC k p ρ => star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x))) :=
    ((Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_cont _ _).comp (Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont p ρ)).star
  have h0 : psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ 0) = 1 := by
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero]
    exact Formalism.FourierDecayAlt.P.Qx5.psi_one (Formalism.FourierDecayAlt.P.LeftFubiniLemmas.inWb_liftVec hz) _
  have h0' : star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ 0)) = 1 := by
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, Formalism.FourierDecayAlt.P.Qx5.psi_one (Formalism.FourierDecayAlt.P.LeftFubiniLemmas.inWb_liftVec hz') _, star_one]
  have := @rcHaar k p ρ
  unfold U.muRC
  exact bump_two volume _ _ hc hc' h0 h0'

end Formalism.FourierDecayAlt.P.CutEX.MkTopBump
