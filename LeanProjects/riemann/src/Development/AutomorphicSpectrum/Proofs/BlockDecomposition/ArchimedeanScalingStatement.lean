import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanScaling
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_scaling : PositivityTheory.PfSWUS.SchInf.ScaleInf := by
  first | exact @GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf | exact GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf | (intros; apply GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf <;> assumption)
