import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFormsToLatticeOfFiniteInvertibleStabilisers
import Mathlib
import Formalism.SatakeDualWeyl.Statement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_forms_to_lattice_of_finite_invertible_stabilisers : ∀ (O : Type) [CommRing O] (G : Type) [Group G] (Γ K : Subgroup G) (B Q : Type) [AddCommGroup B] [Module O B] [AddCommGroup Q] [Module O Q] (ρ : Representation O K B) (π : B →ₗ[O] Q), Function.Surjective π → (∀ κ x, π x = 0 → π (ρ κ x) = 0) → (∀ g : G, Finite {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} ∧ IsUnit ((Nat.card {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} : ℕ) : O)) → ∀ f : G → Q, (∀ (γ : Γ) (g : G) (κ : K) (y : B), f g = π y → f ((γ : G) * g * κ) = π (ρ κ⁻¹ y)) → ∃ F ∈ Formalism.UG.AMFK O Γ K ρ, ∀ g, π (F g) = f g := by
  first | exact @GlobalTheory.lift_forms_of_card_isUnit | exact GlobalTheory.lift_forms_of_card_isUnit | (intros; apply GlobalTheory.lift_forms_of_card_isUnit <;> assumption)
