import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBoundFinitePlaces
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_bound_finite_places : MulF → PairF := by
  first | exact @GlobalTheory.CompanionTheory.Wedge.pairF_of_mulF | exact GlobalTheory.CompanionTheory.Wedge.pairF_of_mulF | (intros; apply GlobalTheory.CompanionTheory.Wedge.pairF_of_mulF <;> assumption)
