import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapDomainRelationLiftCommutingSquare
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mapDomain_relation_lift_commuting_square : ∀ (M : Type 1) [AddCommGroup M] (X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : Type) (c : X₂ → X₄) (d : X₃ → X₄) (u : Y₁ → Y₂) (v : Y₁ → Y₃) (c' : Y₂ → Y₄) (d' : Y₃ → Y₄) (r₂ : X₂ → Y₂) (r₃ : X₃ → Y₃) (r₄ : X₄ → Y₄) (G : Y₄ → Prop), (∀ x, c' (r₂ x) = r₄ (c x)) → (∀ y, d' (r₃ y) = r₄ (d y)) → (∀ x, c' (u x) = d' (v x)) → Function.Injective c' → (∀ x, G (c' x)) → (∀ y, G (d' y) → ∃ x, v x = y) → ∀ (a₂ : X₂ →₀ M) (a₃ : X₃ →₀ M), Finsupp.mapDomain c a₂ + Finsupp.mapDomain d a₃ = 0 → (∀ y ∈ a₃.support, ∀ y' ∈ a₃.support, d y = d y' → r₃ y = r₃ y' ∨ G (d' (r₃ y))) → ∃ a : Y₁ →₀ M, Finsupp.mapDomain u a = Finsupp.mapDomain r₂ a₂ ∧ Finsupp.mapDomain v a = -Finsupp.mapDomain r₃ a₃ := by
  first | (exact @GlobalTheory.mapDomain_corner_lift) | (exact GlobalTheory.mapDomain_corner_lift) | (intros; apply GlobalTheory.mapDomain_corner_lift  <;> assumption)
