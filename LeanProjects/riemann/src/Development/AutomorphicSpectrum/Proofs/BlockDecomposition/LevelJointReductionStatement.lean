import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelJointReduction
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_joint_reduction : PositivityTheory.SiegelWeilFormula.Gunr.JtLev := by
  first | exact @GlobalTheory.CompanionTheory.GunrJt.jtLev | exact GlobalTheory.CompanionTheory.GunrJt.jtLev | (intros; apply GlobalTheory.CompanionTheory.GunrJt.jtLev <;> assumption)
