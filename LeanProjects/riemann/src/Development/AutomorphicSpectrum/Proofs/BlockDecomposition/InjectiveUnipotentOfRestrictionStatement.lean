import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveUnipotentOfRestriction
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_unipotent_of_restriction : PositivityTheory.RgBcC.RealD.InjRL → PositivityTheory.RgBcC.RealD.InjUU := by
  first | exact @GlobalTheory.CompanionTheory.LvChain.injUU_of_injRL | exact GlobalTheory.CompanionTheory.LvChain.injUU_of_injRL | (intros; apply GlobalTheory.CompanionTheory.LvChain.injUU_of_injRL <;> assumption)
