import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeVectorMatrixCoefficients
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToEndDApply
open GlobalTheory.LocFinIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemisimpleModule_repD_of_finite_type_unitary : ∀ (G : Type) [Group G] (K : Set G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (D : Submodule ℂ V) (h1 : (1 : G) ∈ K) (hmul : ∀ k ∈ K, ∀ k' ∈ K, k * k' ∈ K), (∀ k ∈ K, k⁻¹ ∈ K) → ∀ (hst : ∀ k ∈ K, ∀ x ∈ D, ρ k x ∈ D), (∀ x ∈ D, ∃ (m : ℕ) (b : Fin m → V) (A : G → Matrix (Fin m) (Fin m) ℂ), LinearIndependent ℂ b ∧ (∀ i, b i ∈ D) ∧ x ∈ Submodule.span ℂ (Set.range b) ∧ (∀ k ∈ K, ∀ j, ρ k (b j) = ∑ i, A k i j • b i) ∧ (∀ k ∈ K, A k ∈ Matrix.unitaryGroup (Fin m) ℂ)) → IsSemisimpleModule (MonoidAlgebra ℂ (subK K h1 hmul)) (repD ρ D K h1 hmul hst).asModule := by
  first | exact @GlobalTheory.LocFinIso.isSemisimpleModule_repD_of_locally_unitary | exact GlobalTheory.LocFinIso.isSemisimpleModule_repD_of_locally_unitary | (intros; apply GlobalTheory.LocFinIso.isSemisimpleModule_repD_of_locally_unitary <;> assumption)
