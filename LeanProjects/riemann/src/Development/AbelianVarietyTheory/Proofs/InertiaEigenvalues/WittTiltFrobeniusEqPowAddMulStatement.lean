import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittTiltFrobeniusEqPowAddMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CstSApply
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittTiltFrobenius_eq_pow_add_mul : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a), ∃ x : Wq l a, sigma l a w = w ^ l + (l : Wq l a) * x := by
  first | exact @GlobalTheory.FrobCong.sigma_eq_pow_add | exact GlobalTheory.FrobCong.sigma_eq_pow_add | (intros; apply GlobalTheory.FrobCong.sigma_eq_pow_add <;> assumption)
