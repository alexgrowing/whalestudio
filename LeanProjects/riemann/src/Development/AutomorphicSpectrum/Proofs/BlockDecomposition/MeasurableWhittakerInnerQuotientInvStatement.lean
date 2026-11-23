import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableWhittakerInnerQuotientInv
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.UnipotentTateFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantScaled
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralKernelUniformBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantLeSumSwap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateLocalL1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AestronglyMeasurableWhittakerDiagUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Ga
open MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_whittaker_inner_quotient_inv : ∀ (k : ℕ) (Ψ : Ad3.K.LC.Sw), Measurable (fun p : ℂˣ × Ad3.K.LC.M22 => Ad3.K.LC.C.W2 k (Ad3.K.LC.C.innQ Ψ 1 p.2 (p.1 : ℂ)⁻¹) (Matrix.of p.2)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.PerUC.Meas.measurable_whittakerGL2_inner_quotient | exact GlobalTheory.CompanionTheory.PerUC.Meas.measurable_whittakerGL2_inner_quotient | (intros; apply GlobalTheory.CompanionTheory.PerUC.Meas.measurable_whittakerGL2_inner_quotient <;> assumption)
