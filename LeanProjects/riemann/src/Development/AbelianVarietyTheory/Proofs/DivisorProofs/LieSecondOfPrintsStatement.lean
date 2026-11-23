import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar → GlobalTheory.RealLift.LieSecond := by
  first | exact @GlobalTheory.RealLift.LieSecondPf.lieSecond_of_lieScalar | exact GlobalTheory.RealLift.LieSecondPf.lieSecond_of_lieScalar | (intros; apply GlobalTheory.RealLift.LieSecondPf.lieSecond_of_lieScalar <;> assumption)
