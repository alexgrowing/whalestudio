import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIdempotentsOfComaximal
import Mathlib
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigen_idempotents_of_comaximal : ∀ {C : Type} [CommRing C] {A : Type} [CommRing A] {W : Type u} [AddCommGroup W] [Module C W]
  (σ : A →+* Module.End C W) (a : ℕ) (χ : Fin a → A →+* C),
  (∀ i j, i ≠ j → Ideal.span (Set.range fun x => χ i x - χ j x) = ⊤) →
  ∃ e : Fin a → Module.End C W,
    (∀ i (T : Module.End C W), (∀ c, T * σ c = σ c * T) → T * e i = e i * T) ∧
    (∀ i w, (∀ c, σ c w = χ i c • w) → e i w = w) ∧
    (∀ i j w, j ≠ i → (∀ c, σ c w = χ j c • w) → e i w = 0) := by
  first | exact @GlobalTheory.eigenIdempotents_of_comaximal | exact GlobalTheory.eigenIdempotents_of_comaximal | (intros; apply GlobalTheory.eigenIdempotents_of_comaximal <;> assumption)
