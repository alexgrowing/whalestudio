import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTensorIdempotentOfAlgHomToBase
import Mathlib
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensor_idempotent_of_algHom_to_base : ∀ (E K E' : Type) [Field E] [CharZero E] [Field K] [Field E'] [Algebra E K] [Algebra E E'] [FiniteDimensional E E'] (ψ : K ⊗[E] E' →ₐ[K] K), ∃ e : K ⊗[E] E', ψ e = 1 ∧ ∀ a, e * a = algebraMap K (K ⊗[E] E') (ψ a) * e := by
  first | exact @GlobalTheory.exists_tensor_idem_of_algHom | exact GlobalTheory.exists_tensor_idem_of_algHom | (intros; apply GlobalTheory.exists_tensor_idem_of_algHom <;> assumption)
