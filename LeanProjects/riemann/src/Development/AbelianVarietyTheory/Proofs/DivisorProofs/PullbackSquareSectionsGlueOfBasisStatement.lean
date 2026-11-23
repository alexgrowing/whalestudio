import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareSectionsGlueOfBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_square_sections_glue_of_basis : ∀ {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (B : Set X.Opens), (∀ (W : X.Opens) (x : X), x ∈ W → ∃ W' ∈ B, x ∈ W' ∧ W' ≤ W) → (∀ W ∈ B, ∀ (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)), (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a = (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b → ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b) → GlobalTheory.PinchLift.Glues p i i' p' := by
  first | exact @GlobalTheory.PinchLift.glues_of_basis | exact GlobalTheory.PinchLift.glues_of_basis | (intros; apply GlobalTheory.PinchLift.glues_of_basis <;> assumption)
