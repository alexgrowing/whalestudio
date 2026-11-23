import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlurisubharmonicDecreasingLimitExtension
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
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plurisubharmonic_decreasing_limit_extension : ∀ {n : ℕ} {U : Set (V n)}, IsOpen U → ∀ (e : V n → ℝ), ContDiffOn ℝ ∞ e U → (∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (e w : ℂ)) y ξ).re) → (∀ a : ℝ, IsCompact {y | y ∈ U ∧ e y ≤ a}) → ∀ (φ : ℕ → V n → ℝ), (∀ k, ContDiffOn ℝ ∞ (φ k) U) → (∀ k, ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (φ k w : ℂ)) y ξ).re) → (∀ k, ∀ y ∈ U, φ (k + 1) y ≤ φ k y) → ∀ (F0 : V n → ℂ), ContDiffOn ℝ ∞ F0 U → ∀ (h : V n → ℝ≥0∞), Measurable h → (∀ k, ∀ y ∈ U, ∀ ξ : Fin n → ℂ, ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤ h y * ENNReal.ofReal (leviV n (fun w => (φ k w : ℂ)) y ξ).re) → ∀ A : ℝ≥0∞, (∀ k, ∫⁻ y in U, h y * ENNReal.ofReal (Real.exp (-φ k y)) ≤ A) → ∃ F : V n → ℂ, DifferentiableOn ℂ F U ∧ ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F y‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k y)) ≤ A := by
  first | exact @GlobalTheory.HormanderLimit.hormander_limit | exact GlobalTheory.HormanderLimit.hormander_limit | (intros; apply GlobalTheory.HormanderLimit.hormander_limit <;> assumption)
