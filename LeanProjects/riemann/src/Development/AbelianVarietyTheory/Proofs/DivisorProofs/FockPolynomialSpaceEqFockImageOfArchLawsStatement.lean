import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.PolRange := by
  first | exact @GlobalTheory.RealLift.PolRangePf.polRange_of | exact GlobalTheory.RealLift.PolRangePf.polRange_of | (intros; apply GlobalTheory.RealLift.PolRangePf.polRange_of <;> assumption)
