import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentedExactIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.face_map_complex_quasi_iso_iff_epi_exact : ∀ (C : Type 2) [Category.{1} C] [Abelian C] (K : SimplicialObject C) (B : C) (f : K ⟶ (SimplicialObject.const C).obj B), QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex C).map f) ↔ (Epi (f.app (op (SimplexCategory.mk (0)))) ∧ (∃ w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0, (ShortComplex.mk _ _ w).Exact) ∧ ∀ n : ℕ, ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).ExactAt (n + 1)) := by
  first | (exact @GlobalTheory.EtC.AugExact.augmented_exact_iff) | (exact GlobalTheory.EtC.AugExact.augmented_exact_iff) | (intros; apply GlobalTheory.EtC.AugExact.augmented_exact_iff  <;> assumption)
