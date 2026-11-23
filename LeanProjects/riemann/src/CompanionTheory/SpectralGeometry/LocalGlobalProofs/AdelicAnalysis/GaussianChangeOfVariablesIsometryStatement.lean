import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianChangeOfVariablesIsometry
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_change_of_variables_isometry : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) (gi : InfinitePlace F → Matrix ι ι ℝ), B.det ≠ 0 → (∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w)) → (∀ (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ), gauss B ρ P τ (fun w => gi w *ᵥ x w) = gauss B ρ (fun w => (gi w)ᵀ * P w * gi w) τ x) ∧ ∀ τ : InfinitePlace F → ℂ, cG B ρ (fun w => (gi w)ᵀ * P w * gi w) τ = cG B ρ P τ := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.gauss_orth_closed | exact GlobalTheory.CompanionTheory.SW.ThW.gauss_orth_closed | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.gauss_orth_closed <;> assumption)
