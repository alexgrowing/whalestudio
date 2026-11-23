import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.lhs_transfer : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ (δ T : ℝ) (θ : ℝ → ℝ) (F0 : U → ℂ), Continuous θ → Measurable (GlobalTheory.OTY.TwEst.ext0 U F0) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - β i x * GlobalTheory.OTY.TwEst.ext0 U F0 x) y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖(θ (δ * psi A L s x) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β x - F0 x‖ ^ 2 * (wT T (δ * psi A L s x) * Real.exp (-(GlobalTheory.OTY.TwEst.wt A E β z x + psi A L s x)))) ∂vol n (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A E L s U z β h hU htr hq hqm hpsi δ T θ F0 hθ hF0
  have hm : Measurable fun y => δ * psi A L s y := hpsi.const_mul δ
  have hwc : Continuous (wT T) := by
    unfold wT
    refine continuous_const.div (by fun_prop) fun x => ?_
    have : 0 ≤ min (x ^ 2) ((T + 1) ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    linarith
  have hw0 : ∀ x, 0 ≤ wT T x := by
    intro x
    unfold wT
    have : 0 ≤ min (x ^ 2) ((T + 1) ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    positivity
  have key := htr (fun y => (θ (δ * psi A L s y) : ℂ) *
      GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y - GlobalTheory.OTY.TwEst.ext0 U F0 y)
    (fun y => wT T (δ * psi A L s y) * Real.exp (-psi A L s y))
    (((Complex.measurable_ofReal.comp (hθ.measurable.comp hm)).mul hqm).sub hF0)
    ((hwc.measurable.comp hm).mul (Real.measurable_exp.comp hpsi.neg))
    (fun y _ => mul_nonneg (hw0 _) (Real.exp_pos _).le)
  refine Eq.trans ?_ (key.trans ?_)
  · refine setLIntegral_congr_fun hU.measurableSet fun y hy => ?_
    have h1 : GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y
        = GlobalTheory.OTY.TwEst.quot A h β y :=
      GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) ⟨y, hy⟩
    have h2 : (θ (δ * psi A L s y) : ℂ) * h (A.pick y) y
        - β (A.pick y) y * GlobalTheory.OTY.TwEst.ext0 U F0 y
        = β (A.pick y) y * ((θ (δ * psi A L s y) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β y
          - GlobalTheory.OTY.TwEst.ext0 U F0 y) := by
      rw [hq y hy]; ring
    simp only [h1]
    congr 1
    unfold WeightedAtlas.nsq
    simp only [h2, norm_mul, mul_pow]
    ring
  · refine lintegral_congr fun x => ?_
    simp only [GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe]
    congr 2
    rw [neg_add, Real.exp_add]
    ring
