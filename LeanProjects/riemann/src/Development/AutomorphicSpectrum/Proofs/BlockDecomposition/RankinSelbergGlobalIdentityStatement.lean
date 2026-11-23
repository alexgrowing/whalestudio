import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGlobalIdentity
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_global_identity : Ad3.R.B0 → Ad3.R.A1 → Ad3.R.G0 → Ad3.R.G2a → Ad3.R.G4 → Ad3.R.G5 → Ad3.R.GS → Ad3.R.FT → Ad3.R.F2 → Ad3.R.F5 → Ad3.R.F6 → Ad3.R.ConstantTermVanishingAlt → Ad3.R.E6 → Ad3.R.G6 → Ad3.R.X0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.globalIdentity | exact GlobalTheory.CompanionTheory.RankinSelberg.globalIdentity | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.globalIdentity <;> assumption)
