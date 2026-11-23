import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBruhatDecomposition
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_bruhat_decomposition : PositivityTheory.GramSchwartzFunctions.EC.Bruhat := by
  first | exact @GlobalTheory.CompanionTheory.BruhatCell.bruhat | exact GlobalTheory.CompanionTheory.BruhatCell.bruhat | (intros; apply GlobalTheory.CompanionTheory.BruhatCell.bruhat <;> assumption)
