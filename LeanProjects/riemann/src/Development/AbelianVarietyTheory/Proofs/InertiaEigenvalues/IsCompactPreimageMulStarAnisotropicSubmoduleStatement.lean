import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactPreimageMulStarAnisotropicSubmodule
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_preimage_mul_star_anisotropic_submodule : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (V : Submodule E (Matrix (Fin r) (Fin r) E)), (∀ z ∈ V, z * star z = 0 → z = 0) → ∀ B : Set (Matrix (Fin r) (Fin r) E), IsCompact B → IsCompact {z : Matrix (Fin r) (Fin r) E | z ∈ V ∧ z * star z ∈ B} := by
  first | exact @GlobalTheory.mul_star_anisotropic_proper | exact GlobalTheory.mul_star_anisotropic_proper | (intros; apply GlobalTheory.mul_star_anisotropic_proper <;> assumption)
