import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisLogOneAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisEqZeroOfForallDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_acris_log_one_add : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l), GlobalTheory.LogU.InJ w → ∃ y : Per.Acris l, GlobalTheory.LogU.IsLogJ w y := by
  first | exact @GlobalTheory.LogU.exists_isLogJ | exact GlobalTheory.LogU.exists_isLogJ | (intros; apply GlobalTheory.LogU.exists_isLogJ <;> assumption)
