import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicDegreeFormula
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_degree_formula : MulF → MulI → LogAbsBasic → FinSupp → DegAdelic := by
  first | exact @GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of | exact GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of | (intros; apply GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of <;> assumption)
