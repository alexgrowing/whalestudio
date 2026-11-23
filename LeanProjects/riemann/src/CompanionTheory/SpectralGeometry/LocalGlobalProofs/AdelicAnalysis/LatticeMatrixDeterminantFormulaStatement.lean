import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeMatrixDeterminantFormula
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_matrix_determinant_formula : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ)), IsTotallyReal F → (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ), |(gM (ι := ι) ρ (fun v => b v) N).det| = ((N : ℝ) ^ Module.finrank ℚ F * Real.sqrt |(discr F : ℝ)|) ^ Fintype.card ι := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.abs_det_gM_all | exact GlobalTheory.CompanionTheory.SW.ThW.abs_det_gM_all | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.abs_det_gM_all <;> assumption)
