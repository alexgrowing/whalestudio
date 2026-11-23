import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.rhs_le_manifold : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ δ T : ℝ, ∫⁻ x in {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1}, ENNReal.ofReal (‖GlobalTheory.OTY.TwEst.quot A h β x‖ ^ 2 * Real.exp (-(GlobalTheory.OTY.TwEst.wt A E β z x + psi A L s x))) ∂vol n (fun y : U => z y) ≤ ∫⁻ y in {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu := by
  intro n Y _ _ _ _ _ ι La _ A E L s U z β h hU htr hq hm hpsi δ T
  set S : Set Y := {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1} with hS
  have hδ : Measurable fun y => δ * psi A L s y := hpsi.const_mul δ
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const hδ).inter (measurableSet_le hδ measurable_const)
  have hw : Measurable (S.indicator fun y => Real.exp (-psi A L s y)) :=
    (Real.measurable_exp.comp hpsi.neg).indicator hSm
  have key := htr _ _ hm hw (fun y _ => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) y)
  have hS' : MeasurableSet {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1} :=
    measurable_subtype_coe hSm
  rw [← lintegral_indicator hS']
  refine le_trans (le_of_eq ?_) (le_trans key.ge ?_)
  · refine lintegral_congr fun x => ?_
    rw [GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe]
    by_cases hx : (x : Y) ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1} from hx), ← Real.exp_add]
      congr 3
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1} from hx)]
      simp
  · rw [← lintegral_indicator hSm, ← lintegral_indicator hU.measurableSet]
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ U
    · rw [Set.indicator_of_mem hy]
      by_cases hx : y ∈ S
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        have h0 := GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) ⟨y, hy⟩
        simp only at h0
        rw [h0]
        apply le_of_eq
        congr 2
        unfold WeightedAtlas.nsq
        rw [hq y hy, norm_mul]
        ring
      · rw [Set.indicator_of_notMem hx]
        simp
    · rw [Set.indicator_of_notMem hy]
      exact zero_le
