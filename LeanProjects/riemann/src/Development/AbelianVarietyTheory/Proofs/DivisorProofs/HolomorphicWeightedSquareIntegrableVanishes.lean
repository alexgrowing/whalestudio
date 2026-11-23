import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfL
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvariantChartSetLeMulFundamentalSet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.VanishAtSStatementPf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
open scoped ContDiff

namespace GlobalTheory

theorem holo_vanish_of_critical_integrable : ∀ {n : ℕ}, 0 < n → ∀ (u : V n → ℂ) (ρ : ℝ), 0 < ρ → DifferentiableOn ℂ u (Metric.ball 0 ρ) → ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) < ⊤ → u 0 = 0 := by
  intro n hn u ρ hρ hu hint
  by_contra hne
  have hb : Metric.ball (0 : V n) ρ ∈ nhds (0 : V n) := Metric.ball_mem_nhds 0 hρ
  set a := ‖u 0‖ with ha
  have ha0 : 0 < a := norm_pos_iff.mpr hne
  have hc : ContinuousAt u 0 := hu.continuousOn.continuousAt hb
  have ev1 : ∀ᶠ z in nhds (0 : V n), a / 2 < ‖u z‖ :=
    hc.norm.eventually (Ioi_mem_nhds (by show a / 2 < a; linarith))
  obtain ⟨δ0, hδ0, hall⟩ := Metric.eventually_nhds_iff.mp (ev1.and (Filter.eventually_of_mem hb fun z hz => hz))
  set δ := min δ0 ρ with hδ
  have hδpos : 0 < δ := lt_min hδ0 hρ
  have hsub : Metric.ball (0 : V n) δ ⊆ Metric.ball (0 : V n) ρ := Metric.ball_subset_ball (min_le_right _ _)
  have hpt : ∀ z ∈ Metric.ball (0 : V n) δ,
      ENNReal.ofReal ((a / 2) ^ 2) * ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤
        ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) := by
    intro z hz
    have hz0 : dist z 0 < δ0 := by
      rw [Metric.mem_ball] at hz; exact lt_of_lt_of_le hz (min_le_left _ _)
    have h1 := (hall hz0).1
    rw [← ENNReal.ofReal_mul (by positivity), neg_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    have hr : 0 ≤ ‖z‖ ^ (-(2 * (n : ℝ))) := Real.rpow_nonneg (norm_nonneg _) _
    have h2 : (a / 2) ^ 2 ≤ ‖u z‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1.le 2
    exact mul_le_mul_of_nonneg_right h2 hr
  have hlow : ENNReal.ofReal ((a / 2) ^ 2) * ∫⁻ z in Metric.ball (0 : V n) δ, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ)))
      ≤ ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ∫⁻ z in Metric.ball (0 : V n) δ, ENNReal.ofReal ((a / 2) ^ 2) * ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ)))
        ≤ ∫⁻ z in Metric.ball (0 : V n) δ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) :=
          setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt
      _ ≤ _ := lintegral_mono_set hsub
  rw [ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.crit_div hn hδpos,
    ENNReal.mul_top (by simp [ENNReal.ofReal_eq_zero, not_le]; positivity)] at hlow
  exact absurd (lt_of_le_of_lt hlow hint) (lt_irrefl _)

end GlobalTheory
