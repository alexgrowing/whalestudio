import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBasisGeneral
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_basis_general : WedgeF → WedgeI → MulF → MulI → LogAbsBasic → FinSupp → DegBasisG := by
  first | exact @GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of | exact GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of | (intros; apply GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of <;> assumption)
