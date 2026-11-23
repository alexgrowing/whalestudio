import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneParamSubgroup_generators_exist : GlobalTheory.RealLift.GenEx := by
  first | exact @GlobalTheory.RealLiftGen.genEx | exact GlobalTheory.RealLiftGen.genEx | (intros; apply GlobalTheory.RealLiftGen.genEx <;> assumption)
