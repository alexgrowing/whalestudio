import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.only_stable_subspaces : DegSubmod → DegMove → DegBdd → DegPairing → SizeBasic → OnlyStable := by
  first | exact @GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of | exact GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of | (intros; apply GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of <;> assumption)
