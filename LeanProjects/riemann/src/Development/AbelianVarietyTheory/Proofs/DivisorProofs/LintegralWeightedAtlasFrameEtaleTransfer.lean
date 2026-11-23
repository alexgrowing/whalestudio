import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAtlasMeasureEtalePullbackLebesgueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableNsqExtendAndPsiStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.lintegral_frame_transfer : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E : La) (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → ∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A E U z β hE hβ a w ha hw hw0
  classical
  have hUm : MeasurableSet U := hE.isOpen.measurableSet
  have hc := api_nsq_contOn A hE.isOpen hβ.1
  have hm := ContinuousOn.measurable_piecewise hc
    (continuousOn_const (c := (0 : ℝ)) (s := Uᶜ)) hUm
  set N : Y → ℝ := U.piecewise (A.nsq (A.kap + E) β) (fun _ => 0) with hN
  have hNU : ∀ y ∈ U, N y = A.nsq (A.kap + E) β y := fun y hy => by simp [hN, hy]
  have hΦ : Measurable fun y => ENNReal.ofReal (N y * ‖a y‖ ^ 2 * w y) :=
    ENNReal.measurable_ofReal.comp ((hm.mul (ha.norm.pow_const 2)).mul hw)
  rw [setLIntegral_congr_fun hUm
    (g := fun y => ENNReal.ofReal (N y * ‖a y‖ ^ 2 * w y)) (fun y hy => by simp only [hNU y hy]),
    GlobalTheory.T.lintegral_atlasMeasure_etale_pullback_lebesgue n Y ι La A U z hE _ hΦ]
  refine lintegral_congr fun x => ?_
  have hJ : 0 < A.nsq A.kap (jdet A z) x := by
    have := hE.det_ne (A.pick (x : Y)) x x.2 (A.mem_pick _)
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr this) 2) (Real.exp_pos _)
  have hB : 0 < A.nsq (A.kap + E) β x := by
    have : β (A.pick (x : Y)) x ≠ 0 := by
      exact hβ.2 _ x.2
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr this) 2) (Real.exp_pos _)
  have hwx := hw0 x x.2
  rw [hNU x x.2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold GlobalTheory.OTY.TwEst.wt
  rw [neg_add, neg_neg, Real.exp_add, Real.exp_neg, Real.exp_log hB, Real.exp_log hJ]
  ring
