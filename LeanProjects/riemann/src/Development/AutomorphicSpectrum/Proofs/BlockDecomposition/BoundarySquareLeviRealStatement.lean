import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundarySquareLeviReal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_square_levi_real : PositivityTheory.RgBcC.RealD.BdSqL := by
  first | exact @GlobalTheory.CompanionTheory.KPChains.bdSqL | exact GlobalTheory.CompanionTheory.KPChains.bdSqL | (intros; apply GlobalTheory.CompanionTheory.KPChains.bdSqL <;> assumption)
