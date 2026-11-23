import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteFormBounds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteFormBoundsStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FormVal
theorem form_value_eq_finite_mul_infinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinFormK ∧ InfFormK := fun _ =>
  form_fin_inf_of GlobalTheory.T.integralGoodForm_values_mem_scaledDualWeylLattice GlobalTheory.T.baseTupleGoodForm_values_bounded_by_classSum GlobalTheory.T.kernelLossBound_nonneg_and_level_card_le_exp
end GlobalTheory.FormVal
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_value_finite_infinite_factorization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinFormK ∧ InfFormK := by
  first | exact @_root_.GlobalTheory.FormVal.form_value_eq_finite_mul_infinite | exact _root_.GlobalTheory.FormVal.form_value_eq_finite_mul_infinite | (intros; apply _root_.GlobalTheory.FormVal.form_value_eq_finite_mul_infinite <;> assumption)
end
