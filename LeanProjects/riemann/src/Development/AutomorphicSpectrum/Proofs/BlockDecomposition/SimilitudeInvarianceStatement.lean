import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeInvariance
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_invariance : Simil := by
  first | exact @GlobalTheory.CompanionTheory.SW.MassSimil.simil | exact GlobalTheory.CompanionTheory.SW.MassSimil.simil | (intros; apply GlobalTheory.CompanionTheory.SW.MassSimil.simil <;> assumption)
