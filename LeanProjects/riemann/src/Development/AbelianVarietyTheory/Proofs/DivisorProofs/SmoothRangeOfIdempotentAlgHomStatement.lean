import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothRangeOfIdempotentAlgHom
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_range_of_idempotent_algHom : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Smooth R A] (e : A →ₐ[R] A), (∀ x, e (e x) = e x) → Algebra.Smooth R e.range := by
  first | exact @GlobalTheory.smooth_range_of_idempotent | exact GlobalTheory.smooth_range_of_idempotent | (intros; apply GlobalTheory.smooth_range_of_idempotent <;> assumption)
