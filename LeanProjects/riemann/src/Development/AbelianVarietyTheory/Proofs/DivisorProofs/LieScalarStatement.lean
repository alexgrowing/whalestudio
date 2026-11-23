import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieScalar_of_prints_derEx_vacLine : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar := by
  first | exact @GlobalTheory.LieScal.lieScalar | exact GlobalTheory.LieScal.lieScalar | (intros; apply GlobalTheory.LieScal.lieScalar <;> assumption)
