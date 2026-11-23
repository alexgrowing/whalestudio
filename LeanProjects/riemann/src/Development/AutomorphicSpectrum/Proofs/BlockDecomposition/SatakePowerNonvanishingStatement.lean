import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakePowerNonvanishing
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_power_nonvanishing : PositivityTheory.SphericalProduct.SatPowNonvan := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.satPowNonvan | exact GlobalTheory.CompanionTheory.SatPow.satPowNonvan | (intros; apply GlobalTheory.CompanionTheory.SatPow.satPowNonvan <;> assumption)
