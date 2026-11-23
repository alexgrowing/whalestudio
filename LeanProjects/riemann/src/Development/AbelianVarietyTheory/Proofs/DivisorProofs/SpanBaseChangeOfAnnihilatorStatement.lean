import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanBaseChangeOfAnnihilator
import Mathlib

open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_base_change_of_annihilator : ∀ (F R : Type) [Field F] [CommRing R] [Algebra F R] (κ : Type) [Fintype κ] (A : Set (κ → F)) (x : κ → R),
    (∀ y : κ → F, (∀ a ∈ A, a ⬝ᵥ y = 0) → x ⬝ᵥ (fun i => algebraMap F R (y i)) = 0) →
    x ∈ Submodule.span R ((fun a : κ → F => fun i => algebraMap F R (a i)) '' A) := by
  first | exact @GlobalTheory.mem_span_image_of_orthogonal_rational_annihilator | exact GlobalTheory.mem_span_image_of_orthogonal_rational_annihilator | (intros; apply GlobalTheory.mem_span_image_of_orthogonal_rational_annihilator <;> assumption)
