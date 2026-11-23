import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSplittingUnitFaithfullyFlat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_splitting_unit_faithfullyFlat : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Finite R D →
    Module.Projective R D → Module.FaithfullyFlat R D → ∃ τ : D →ₗ[R] R, τ 1 = 1 := by
  first | (exact @GlobalTheory.unit_splits_of_projective_faithfullyFlat) | (exact GlobalTheory.unit_splits_of_projective_faithfullyFlat) | (intros; apply GlobalTheory.unit_splits_of_projective_faithfullyFlat  <;> assumption)
