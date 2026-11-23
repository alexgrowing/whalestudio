import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralOrIsIntegralInvInFieldFactor
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_or_isIntegral_inv_in_fieldFactor : ∀ (K : UQ) (B : InvAlg K) (f y z : B.A), IsIdempotentElem f → (∀ w, f * w ≠ 0 → ∃ v, f * w * v = f) → f * y * z = f → IsIntegral K.O (f * y) ∨ IsIntegral K.O (f * z) := by
  first | exact @GlobalTheory.UnitLemma.Desc.isIntegral_or_isIntegral_of_fieldFactor | exact GlobalTheory.UnitLemma.Desc.isIntegral_or_isIntegral_of_fieldFactor | (intros; apply GlobalTheory.UnitLemma.Desc.isIntegral_or_isIntegral_of_fieldFactor <;> assumption)
