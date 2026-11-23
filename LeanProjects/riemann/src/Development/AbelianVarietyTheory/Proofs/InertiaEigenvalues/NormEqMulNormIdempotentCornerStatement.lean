import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqMulNormIdempotentCorner
import Mathlib
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eq_mul_norm_idempotent_corner : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (ψ : A →ₐ[K] K) (e : A), ψ e = 1 → (∀ a, e * a = algebraMap K A (ψ a) * e) → ∀ a : A, Algebra.norm K a = ψ a * Algebra.norm K (e + (1 - e) * a) := by
  first | exact @GlobalTheory.norm_eq_mul_norm_idem_corner | exact GlobalTheory.norm_eq_mul_norm_idem_corner | (intros; apply GlobalTheory.norm_eq_mul_norm_idem_corner <;> assumption)
