import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryModelHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_model_holds : UModel := by
  first | exact @GlobalTheory.CompanionTheory.UMod.uModel | exact GlobalTheory.CompanionTheory.UMod.uModel | (intros; apply GlobalTheory.CompanionTheory.UMod.uModel <;> assumption)
