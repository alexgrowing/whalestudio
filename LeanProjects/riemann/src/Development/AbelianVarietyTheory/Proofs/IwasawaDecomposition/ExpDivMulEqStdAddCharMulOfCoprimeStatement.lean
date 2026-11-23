import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpDivMulEqStdAddCharMulOfCoprime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTrace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_div_mul_eq_stdAddChar_mul_of_coprime : ∀ (p q : ℕ) [NeZero p] [NeZero q], Nat.Coprime p q → ∀ T : ℤ, Complex.exp (2 * Real.pi * Complex.I * (T : ℂ) / ((p * q : ℕ) : ℂ)) = ZMod.stdAddChar (((q : ZMod p))⁻¹ * (T : ZMod p)) * ZMod.stdAddChar (((p : ZMod q))⁻¹ * (T : ZMod q)) := by
  first | exact @GlobalTheory.exp_two_pi_I_div_mul_eq_stdAddChar_mul | exact GlobalTheory.exp_two_pi_I_div_mul_eq_stdAddChar_mul | (intros; apply GlobalTheory.exp_two_pi_I_div_mul_eq_stdAddChar_mul <;> assumption)
