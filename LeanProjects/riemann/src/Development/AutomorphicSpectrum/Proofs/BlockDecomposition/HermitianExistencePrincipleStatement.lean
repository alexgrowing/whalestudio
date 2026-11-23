import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianExistencePrinciple
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_existence_principle : HEx := by
  first | exact @GlobalTheory.CompanionTheory.RgBase.hEx | exact GlobalTheory.CompanionTheory.RgBase.hEx | (intros; apply GlobalTheory.CompanionTheory.RgBase.hEx <;> assumption)
