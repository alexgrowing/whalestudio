import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenProjectionsOfComaximal
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigen_projections_tensor_of_comaximal : ∀ (R F : Type) [CommRing R] [CommRing F] (a : ℕ) (t : Fin a → (F →+* R)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → ∃ e : Fin a → R ⊗[ℤ] F, ∀ (M : Type) [AddCommGroup M] (Θ : R ⊗[ℤ] F →+* AddMonoid.End M) (i l : Fin a) (m : M), (∀ c : F, Θ (1 ⊗ₜ c) m = Θ (t l c ⊗ₜ 1) m) → Θ (e i) m = if i = l then m else 0 := by
  first | (exact @GlobalTheory.eigenProjections_of_comaximal) | (exact GlobalTheory.eigenProjections_of_comaximal) | (intros; apply GlobalTheory.eigenProjections_of_comaximal  <;> assumption)
