import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRootMapMinpolyIffExistsRingHomExtension

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRoot_map_minpoly_iff_exists_ringHom_extension : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B], Function.Injective (algebraMap A B) → ∀ (g : B) (φ : A →+* ℂ) (z : ℂ), ((minpoly A g).map φ).IsRoot z ↔ ∃ x : B →+* ℂ, x.comp (algebraMap A B) = φ ∧ x g = z := by
  first | exact @GlobalTheory.isRoot_map_minpoly_iff_exists_ringHom | exact GlobalTheory.isRoot_map_minpoly_iff_exists_ringHom | (intros; apply GlobalTheory.isRoot_map_minpoly_iff_exists_ringHom <;> assumption)
