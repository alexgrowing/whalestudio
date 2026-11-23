import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionLocalIntegers
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_retraction_localIntegers : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1), ∃ r : ↥(OL LL') →+ ↥(OL LL), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) ∧ r 1 = 1 := by
  first | exact @GlobalTheory.UseLoc.exists_intRetraction | exact GlobalTheory.UseLoc.exists_intRetraction | (intros; apply GlobalTheory.UseLoc.exists_intRetraction <;> assumption)
