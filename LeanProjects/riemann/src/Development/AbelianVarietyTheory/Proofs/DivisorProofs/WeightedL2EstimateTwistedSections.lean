import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.cutoff_quot_wint_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ (δ : ℝ) (θ : ℝ → ℝ), Continuous θ → (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) → wint n (fun y : U => z y) (fun x : U => (θ (δ * psi A L s x) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β x) (fun x : U => GlobalTheory.OTY.TwEst.wt A E β z x) ≤ ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu := by
  intro n Y _ _ _ _ _ ι La _ A E L s U z β h hU htr hq hm hpsi δ θ hθ hθ1
  have hma : Measurable (fun y : Y => (θ (δ * psi A L s y) : ℂ) * GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y) :=
    (Complex.measurable_ofReal.comp (hθ.measurable.comp (hpsi.const_mul δ))).mul hm
  have key := htr _ (fun _ => 1) hma measurable_const (fun _ _ => zero_le_one)
  simp only [GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe, one_mul, mul_one] at key
  unfold wint
  rw [← key]
  refine le_trans (setLIntegral_mono' hU.measurableSet ?_) (setLIntegral_le_lintegral U _)
  intro y hy
  apply ENNReal.ofReal_le_ofReal
  have e : GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y = GlobalTheory.OTY.TwEst.quot A h β y :=
    GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) ⟨y, hy⟩
  rw [e]
  unfold WeightedAtlas.nsq
  rw [hq y hy, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hθ1 _).1]
  obtain ⟨h0, h1⟩ := hθ1 (δ * psi A L s y)
  have h2 : θ (δ * psi A L s y) ^ 2 ≤ 1 := by nlinarith
  set t := θ (δ * psi A L s y)
  set b := ‖β (A.pick y) y‖
  set q := ‖GlobalTheory.OTY.TwEst.quot A h β y‖
  generalize hc : Real.exp _ = c
  have hc0 : 0 ≤ c := hc ▸ (Real.exp_pos _).le
  have h3 : 0 ≤ (b * q) ^ 2 * c := by positivity
  calc b ^ 2 * c * (t * q) ^ 2 = t ^ 2 * ((b * q) ^ 2 * c) := by ring
    _ ≤ 1 * ((b * q) ^ 2 * c) := mul_le_mul_of_nonneg_right h2 h3
    _ = _ := one_mul _
