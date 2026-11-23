import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageExpectedCount
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_theta_average_le_of_countData : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ φ : (ι → A F) → ℂ, SB φ → ∀ κ t : ℝ, 0 < κ → 0 < t → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, t ≤ (τ w).im) → (∀ v w, κ * (τ w).im ≤ (τ v).im) → (∀ x, Measurable fun ω => thTerm B ρ P (gf ω) (gi ω) φ τ x) ∧ ENNReal.ofReal (wt M τ) * ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr ≤ ENNReal.ofReal C := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.ThetaBound.theta_integral_bound | exact GlobalTheory.CompanionTheory.SW.Core.ThetaBound.theta_integral_bound | (intros; apply GlobalTheory.CompanionTheory.SW.Core.ThetaBound.theta_integral_bound <;> assumption)
