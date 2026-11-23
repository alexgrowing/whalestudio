import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Gl2ComplexIwasawaDecomposition
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gl2_complex_iwasawa_decomposition_upper_unitary : ∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.det ≠ 0 → ∃ (κ : Matrix (Fin 2) (Fin 2) ℂ) (b : ℂ) (R : ℝ),
    0 < R ∧ R ^ 2 = ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 ∧ κ * κᴴ = 1 ∧ ‖κ.det‖ = 1 ∧
      g = !![g.det / (R : ℂ), b; 0, (R : ℂ)] * κ := by
  first | exact @GlobalTheory.CompanionTheory.GodementFE.Iwasawa.gl2_complex_iwasawa | exact GlobalTheory.CompanionTheory.GodementFE.Iwasawa.gl2_complex_iwasawa | (intros; apply GlobalTheory.CompanionTheory.GodementFE.Iwasawa.gl2_complex_iwasawa <;> assumption)
