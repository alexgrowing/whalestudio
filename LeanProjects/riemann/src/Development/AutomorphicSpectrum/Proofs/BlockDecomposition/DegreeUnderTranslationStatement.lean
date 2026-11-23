import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeUnderTranslation
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_under_translation : MulF → MulI → SzFin → FinSupp → DegBasisG → DegMove := by
  first | exact @GlobalTheory.CompanionTheory.DegMoveProof.degMove_of | exact GlobalTheory.CompanionTheory.DegMoveProof.degMove_of | (intros; apply GlobalTheory.CompanionTheory.DegMoveProof.degMove_of <;> assumption)
