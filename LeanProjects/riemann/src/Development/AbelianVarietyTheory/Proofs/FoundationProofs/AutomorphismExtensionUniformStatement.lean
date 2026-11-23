import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphismExtensionUniform
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5 Polynomial
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphism_extension_uniform : ∀ (Ω L K : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Field L] [IsAlgClosed L] [Field K] [CharZero K] [Algebra K L] [Algebra.IsAlgebraic K L] (j : Ω →+* L) (s : Ω ≃ₐ[ℚ] Ω), (∀ x : Ω, ∃ g : L ≃ₐ[K] L, g (j x) = j (s x)) → ∃ g : L ≃ₐ[K] L, ∀ x : Ω, g (j x) = j (s x) := by
  first | exact @GlobalTheory.exists_algEquiv_inducing_of_forall_conj | exact GlobalTheory.exists_algEquiv_inducing_of_forall_conj | (intros; apply GlobalTheory.exists_algEquiv_inducing_of_forall_conj <;> assumption)
