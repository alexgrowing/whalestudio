import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusFixedTensorEqConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_fixed_tensor_eq_constant : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) (k : Type) [Field k] [Algebra ↥(OL LL) k] [CharP k l] (x : k ⊗[↥(OL LL)] RW LL), Algebra.TensorProduct.map (AlgHom.id k k) (φRW LL) x = x → ∃ c : k, x = algebraMap k (k ⊗[↥(OL LL)] RW LL) c := by
  first | exact @GlobalTheory.RedFixed.fixed_red | exact GlobalTheory.RedFixed.fixed_red | (intros; apply GlobalTheory.RedFixed.fixed_red <;> assumption)
