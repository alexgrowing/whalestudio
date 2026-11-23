import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDeriva
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx := by
  first | exact @GlobalTheory.FockMapEx.fockEx_of_derEx | exact GlobalTheory.FockMapEx.fockEx_of_derEx | (intros; apply GlobalTheory.FockMapEx.fockEx_of_derEx <;> assumption)
