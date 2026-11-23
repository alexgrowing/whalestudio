import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryBorelSplitting
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_borel_splitting : PositivityTheory.SphericalProduct.BorelSplitU := by
  first | exact @GlobalTheory.CompanionTheory.BorelSplit.borelSplitU | exact GlobalTheory.CompanionTheory.BorelSplit.borelSplitU | (intros; apply GlobalTheory.CompanionTheory.BorelSplit.borelSplitU <;> assumption)
