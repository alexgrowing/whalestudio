import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityOfMassOne
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_density_of_mass_one : Scal → PositivityTheory.SiegelWeilFormula.Densx.MassOne → LocR := by
  first | exact @GlobalTheory.CompanionTheory.RankOneLoc.locR | exact GlobalTheory.CompanionTheory.RankOneLoc.locR | (intros; apply GlobalTheory.CompanionTheory.RankOneLoc.locR <;> assumption)
