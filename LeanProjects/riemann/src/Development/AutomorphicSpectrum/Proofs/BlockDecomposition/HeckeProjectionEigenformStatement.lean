import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeProjectionEigenform
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_projection_eigenform : Ad3.R.B0 → Ad3.R.C1 → Ad3.R.G1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.F3 → Ad3.R.F5 → Ad3.R.G6 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.g6 | exact GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.g6 | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.g6 <;> assumption)
