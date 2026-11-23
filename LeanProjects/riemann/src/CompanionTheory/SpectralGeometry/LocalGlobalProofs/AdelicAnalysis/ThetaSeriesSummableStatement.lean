import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaSeriesSummable
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_summable : ∀ (F : Type) [Field F] [NumberField F], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ), IsOrth B ρ gf gi → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → (∀ φ : (ι → A F) → ℂ, SB φ → Summable fun x => ‖thTerm B ρ P gf gi φ τ x‖) ∧ ∃ φ : (ι → A F) → ℂ, SB φ ∧ theta B ρ P gf gi φ τ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaSum.theta_summable_and_ne_zero | exact GlobalTheory.CompanionTheory.SW.ThetaSum.theta_summable_and_ne_zero | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaSum.theta_summable_and_ne_zero <;> assumption)
