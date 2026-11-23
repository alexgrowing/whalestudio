import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPickReal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_pick_real : PositivityTheory.RgBcC.RealD.InvPick := by
  first | exact @GlobalTheory.CompanionTheory.InvPickKP.invPick | exact GlobalTheory.CompanionTheory.InvPickKP.invPick | (intros; apply GlobalTheory.CompanionTheory.InvPickKP.invPick <;> assumption)
