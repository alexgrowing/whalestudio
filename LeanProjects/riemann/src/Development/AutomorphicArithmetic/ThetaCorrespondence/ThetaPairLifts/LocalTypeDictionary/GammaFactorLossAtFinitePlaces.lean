import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGammaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGammaBoundStatement

section
open NumberField
namespace GlobalTheory.GamLoss
variable {E : Type} [Field E] [NumberField E]
end GlobalTheory.GamLoss
namespace GlobalTheory.GamLoss
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FunObj
variable {D : D7}
end GlobalTheory.GamLoss
namespace GlobalTheory.GamLoss
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
variable {D : D7}
end GlobalTheory.GamLoss
namespace GlobalTheory.GamLoss
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SumSize GlobalTheory.RowTest
open Formalism.DivisionValues (vw lw)
variable {D : D7}
end GlobalTheory.GamLoss
namespace GlobalTheory.GamLoss
open GlobalTheory.SumSize GlobalTheory.RowClaim
theorem finite_place_gamma_loss_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinGamK := by
  intro _
  refine ⟨0, fun CF _ => ⟨90, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ _ => ?_⟩⟩⟩
  have hL : (1 : ℝ) ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hb : (1 : ℝ) ≤ large₂.sc.b := Real.one_le_exp (by linarith)
  have hlb : (1 : ℝ) ≤ Real.log large₂.sc.b := by
    show (1 : ℝ) ≤ Real.log (Real.exp large₂.sc.L)
    rw [Real.log_exp]; exact hL
  exact finGamAt_of ch hC hb hlb
end GlobalTheory.GamLoss
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gamma_factor_loss_at_finite_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinGamK := by
  first | exact @_root_.GlobalTheory.GamLoss.finite_place_gamma_loss_bound | exact _root_.GlobalTheory.GamLoss.finite_place_gamma_loss_bound | (intros; apply _root_.GlobalTheory.GamLoss.finite_place_gamma_loss_bound <;> assumption)
end
