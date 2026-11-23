import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IteratedColumnTransformEqGlobalWhittaker
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import GroundTheory.GlobalFields.TateThesis.AdelicChar
open NumberField Matrix GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedColumnTransform_eq_globalWhittaker : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), 0 < a → Continuous F → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → GlobalTheory.CuspGeneric.whit (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) (a - 1) F = GlobalTheory.JSW.whit F := by
  first | exact @GlobalTheory.CuspGeneric.WhitEq.whit_eq_whittaker | exact GlobalTheory.CuspGeneric.WhitEq.whit_eq_whittaker | (intros; apply GlobalTheory.CuspGeneric.WhitEq.whit_eq_whittaker <;> assumption)
