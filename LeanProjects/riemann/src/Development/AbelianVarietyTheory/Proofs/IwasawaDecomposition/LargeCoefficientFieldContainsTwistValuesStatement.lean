import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LargeCoefficientFieldContainsTwistValues
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField : Top.EvLg fun _ B f T => ∀ (px : PreX B.toPre) (I : Col2.ColIn B px) (hX : B.fields.Ok), I.Ok → I.C = f → Set.range I.xi = T.set f → ValsIn I ∧ ∀ U Xg tr, (∀ χ ∈ Xg, IsAbsIrrChar χ) → (famC I hX U Xg tr).fam3.Ok3 1 := by
  first | exact @GlobalTheory.Mem.R3.OkVals.large_coefficientField_contains_twist_values | exact GlobalTheory.Mem.R3.OkVals.large_coefficientField_contains_twist_values | (intros; apply GlobalTheory.Mem.R3.OkVals.large_coefficientField_contains_twist_values <;> assumption)
