import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterSideEquidistribution
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_side_equidistribution : PositivityTheory.Rg.Mass.Equi → PsiSide := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.psiSide_of_equi | exact GlobalTheory.CompanionTheory.BasePsi.psiSide_of_equi | (intros; apply GlobalTheory.CompanionTheory.BasePsi.psiSide_of_equi <;> assumption)
