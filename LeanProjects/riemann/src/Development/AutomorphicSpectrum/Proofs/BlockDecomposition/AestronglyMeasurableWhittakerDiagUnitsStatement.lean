import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AestronglyMeasurableWhittakerDiagUnits
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aestronglyMeasurable_whittaker_diag_units : ∀ (k : ℕ) (f : SchwartzMap (Fin 2 → ℂ) ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ),
    AEStronglyMeasurable (fun a : ℂˣ => W2 k f (d2 a * g)) mulC := by
  first | exact @GlobalTheory.CompanionTheory.GodementFE.aestronglyMeasurable_whittakerGL2_diag | exact GlobalTheory.CompanionTheory.GodementFE.aestronglyMeasurable_whittakerGL2_diag | (intros; apply GlobalTheory.CompanionTheory.GodementFE.aestronglyMeasurable_whittakerGL2_diag <;> assumption)
