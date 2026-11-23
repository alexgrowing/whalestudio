import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorResidueUnramifiedFinite
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_residue_unramified_finite : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [IsLocalRing R] [Algebra A B] [Algebra A R], ((IsLocalRing.residue R).comp (algebraMap A R)).Finite → ((IsLocalRing.residue R).comp (algebraMap A R)).FormallyUnramified → Algebra.FormallyUnramified B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) ∧ Module.Finite B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) := by
  first | exact @GlobalTheory.tensor_quot_maximalIdeal_finite_formallyUnramified | exact GlobalTheory.tensor_quot_maximalIdeal_finite_formallyUnramified | (intros; apply GlobalTheory.tensor_quot_maximalIdeal_finite_formallyUnramified <;> assumption)
