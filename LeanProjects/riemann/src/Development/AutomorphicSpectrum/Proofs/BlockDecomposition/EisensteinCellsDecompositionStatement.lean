import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCellsDecomposition
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Unfold2
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_cells_decomposition : PositivityTheory.GramSchwartzFunctions.EC.Bruhat → PositivityTheory.GramSchwartzFunctions.EC.RatPts → PositivityTheory.GramSchwartzFunctions.EC.PInv → PositivityTheory.GramSchwartzFunctions.EC.Term2 → PositivityTheory.GramSchwartzFunctions.EisCells := by
  first | exact @GlobalTheory.CompanionTheory.EisCellsAsm.eisCells_of | exact GlobalTheory.CompanionTheory.EisCellsAsm.eisCells_of | (intros; apply GlobalTheory.CompanionTheory.EisCellsAsm.eisCells_of <;> assumption)
