import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFormulaOfTotalMassOne
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_formula_of_total_mass_one : PositivityTheory.SiegelWeilFormula.Densx.MassOne → Prop1 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.Rank.mass_formula_of_total_mass_one | exact GlobalTheory.CompanionTheory.Mass.Rank.mass_formula_of_total_mass_one | (intros; apply GlobalTheory.CompanionTheory.Mass.Rank.mass_formula_of_total_mass_one <;> assumption)
