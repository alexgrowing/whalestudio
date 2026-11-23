import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRelationsReal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_relations_real : PositivityTheory.RgBcC.RealD.LevRel := by
  first | exact @GlobalTheory.CompanionTheory.LevChainRel.levRel | exact GlobalTheory.CompanionTheory.LevChainRel.levRel | (intros; apply GlobalTheory.CompanionTheory.LevChainRel.levRel <;> assumption)
