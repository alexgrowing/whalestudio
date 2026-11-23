import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiscreteSpectrum
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.FinCut

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_discrete_spectrum : PositivityTheory.Rg.BcB.F.F5.FinDiscN := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscN.finDiscN | exact GlobalTheory.CompanionTheory.FinDiscN.finDiscN | (intros; apply GlobalTheory.CompanionTheory.FinDiscN.finDiscN <;> assumption)
