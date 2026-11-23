import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSubgroupKilledNearPointOfFibre
import Mathlib
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_subgroup_killed_near_point_of_fibre : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (Z : Over S') (i : Z ⟶ G) (V₀ : S'.Opens) (d : ℕ) (s : S'), Mono i → s ∈ V₀ → IsFinite (Z.hom ∣_ V₀) → (∀ T : Over S', Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ z : T ⟶ Z, z ≫ i = 1) → (∀ (T : Over S') (a b : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i) * (b ≫ i)) → (∀ (T : Over S') (a : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i)⁻¹) → IsUnit ((d : ℕ) : S'.residueField s) → (∀ (T : Over S') (z : T ⟶ Z), (∃ f : T.left ⟶ Spec (S'.residueField s), T.hom = f ≫ S'.fromSpecResidueField s) → (z ≫ i) ^ d = 1) → ∃ V : S'.Opens, s ∈ V ∧ V ≤ V₀ ∧ ∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V : Set S') → (z ≫ i) ^ d = 1 := by
  first | (exact @GlobalTheory.FiniteKilled.killed_near) | (exact GlobalTheory.FiniteKilled.killed_near) | (intros; apply GlobalTheory.FiniteKilled.killed_near  <;> assumption)
