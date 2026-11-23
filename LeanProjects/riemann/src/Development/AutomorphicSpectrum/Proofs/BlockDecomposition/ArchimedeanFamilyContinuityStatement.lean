import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFamilyContinuity
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_family_continuity : PositivityTheory.PfSWUS.SchInf.FamCont := by
  first | exact @GlobalTheory.CompanionTheory.PushFam.integrable_continuousAt_of_linear_push | exact GlobalTheory.CompanionTheory.PushFam.integrable_continuousAt_of_linear_push | (intros; apply GlobalTheory.CompanionTheory.PushFam.integrable_continuousAt_of_linear_push <;> assumption)
