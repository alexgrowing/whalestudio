import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHormanderPeakCutoffSingularWeights
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
theorem _root_.GlobalTheory.T.exists_hormanderPeak_cutoff_singularWeights : ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → C1 * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → C1 * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a) → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∃ (ρ c : ℝ) (F0 : V (nd X) → ℂ) (ψ : ℕ → Frame X.Ψ r → ℝ) (φ : ℕ → V (nd X) → ℝ) (h : V (nd X) → ℝ≥0∞), 0 < ρ ∧ ρ ≤ 1 / (100 * (r : ℝ) ^ 2) ∧ 0 < c ∧ Metric.closedBall (0 : V (nd X)) ρ ⊆ OmF X x ∧ muF X x (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) < ⊤ ∧ ContDiffOn ℝ ∞ F0 (OmF X x) ∧ (∀ z, ‖z‖ ≤ ρ / 2 → F0 z = 1) ∧ (∀ z, ρ ≤ ‖z‖ → F0 z = 0) ∧ (∀ z, ‖F0 z‖ ≤ 1) ∧ (∀ k, Measurable (ψ k)) ∧ (∀ k, ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ k (rmul y b) = ψ k y) ∧ (∀ k, ∀ γ ∈ X.Γ, ∀ y ∈ X.dom, ψ k (lact γ y) = ψ k y) ∧ (∀ k y, ψ k y ≤ 0) ∧ (∀ k, ∀ z ∈ OmF X x, φ k z = phla X la (cpt X x z) - (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) * rhF X x z - Real.log (densF X x z) + ψ k (cpt X x z)) ∧ (∀ k, ContDiffOn ℝ ∞ (φ k) (OmF X x)) ∧ (∀ k, ∀ z ∈ OmF X x, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ (leviV (nd X) (fun w => ((φ k w : ℝ) : ℂ)) z ξ).re) ∧ (∀ k, ∀ z ∈ OmF X x, φ (k + 1) z ≤ φ k z) ∧ Measurable h ∧ (∀ k, ∀ z ∈ OmF X x, ∀ ξ : Fin (nd X) → ℂ, ENNReal.ofReal (‖∑ j, wdb (nd X) j F0 z * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤ h z * ENNReal.ofReal (leviV (nd X) (fun w => ((φ k w : ℝ) : ℂ)) z ξ).re) ∧ (∀ k, ∫⁻ z in OmF X x, h z * ENNReal.ofReal (Real.exp (-φ k z)) ≤ ENNReal.ofReal (Real.exp (C1 * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))) * muF X x (Metric.ball 0 ρ ∩ OmF X x)) ∧ (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, Real.exp (-phla X la (cpt X x z)) * Real.exp ((4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) * rhF X x z) ≤ Real.exp (C1 * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))) ∧ (∀ w ∈ Metric.ball (0 : V (nd X)) (ρ / 2), ENNReal.ofReal (c * ‖w‖ ^ (-(2 * (nd X : ℝ)))) ≤ ⨆ k, ENNReal.ofReal (Real.exp (-ψ k (cpt X x w)))) ∧ (∀ w ∈ Metric.ball (0 : V (nd X)) (ρ / 2), ENNReal.ofReal (c * ‖w‖ ^ (-(2 * (nd X : ℝ)))) ≤ ⨆ k, ENNReal.ofReal (Real.exp (-φ k w))) := by
  first | exact @GlobalTheory.PeakWeight.peak_weight | exact GlobalTheory.PeakWeight.peak_weight | (intros; apply GlobalTheory.PeakWeight.peak_weight <;> assumption)
