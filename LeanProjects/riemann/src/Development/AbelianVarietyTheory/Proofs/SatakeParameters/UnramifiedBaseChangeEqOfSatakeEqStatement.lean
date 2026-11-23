import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedBaseChangeEqOfSatakeEq
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
open Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedBaseChange_eq_of_satake_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (α : Fin (n / 2) → ℂˣ) (α₀ : Fin (n / 2) → ℂ), (∀ (d : Fin n → ℤ) (t : Formalism.UG.GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → Formalism.UG.SatU ϖ q (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) t) (fun i => (α i : ℂ)) = Formalism.UG.SatU ϖ q (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) t) α₀) → (GlobalTheory.LGrp.bcParam n α).map (fun a : ℂˣ => (a : ℂ)) = ubc n (Finset.univ.val.map α₀) := by
  first | exact @GlobalTheory.SatBcInj.bcParam_eq_ubc_of_satU_eq | exact GlobalTheory.SatBcInj.bcParam_eq_ubc_of_satU_eq | (intros; apply GlobalTheory.SatBcInj.bcParam_eq_ubc_of_satU_eq <;> assumption)
