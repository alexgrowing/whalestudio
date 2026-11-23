import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegBasisOfDegBasisG
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degBasis_of_degBasisG' : DegBasisG → DegBasis := by
  first | exact @GlobalTheory.CompanionTheory.DegreeBasis.degBasis_of_degBasisG | exact GlobalTheory.CompanionTheory.DegreeBasis.degBasis_of_degBasisG | (intros; apply GlobalTheory.CompanionTheory.DegreeBasis.degBasis_of_degBasisG <;> assumption)
