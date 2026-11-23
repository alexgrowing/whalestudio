import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldExtensionOfIntegralRetraction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fieldExtension_of_integral_retraction : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL)), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) → r 1 = 1 → ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧ ∀ x : ↥(OL LL'), p (x : ↥LL'.1) = ((r x : ↥(OL LL)) : ↥LL.1) := by
  first | exact @GlobalTheory.UseLoc.extRet_exists | exact GlobalTheory.UseLoc.extRet_exists | (intros; apply GlobalTheory.UseLoc.extRet_exists <;> assumption)
