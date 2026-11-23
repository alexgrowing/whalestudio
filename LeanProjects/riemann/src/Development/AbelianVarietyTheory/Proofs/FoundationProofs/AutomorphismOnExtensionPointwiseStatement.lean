import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphismOnExtensionPointwise
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5 Polynomial
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphism_on_extension_pointwise : ∀ (Ω L K : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Field L] [IsAlgClosed L] [Field K] [CharZero K] [Algebra K L] [Algebra.IsAlgebraic K L] (j : Ω →+* L) (s : Ω ≃ₐ[ℚ] Ω), (∀ a : Ω, j a ∈ Set.range (algebraMap K L) → s a = a) → ∀ x : Ω, ∃ g : L ≃ₐ[K] L, g (j x) = j (s x) := by
  first | exact @GlobalTheory.exists_algEquiv_apply_eq_of_fixes_preimage_base | exact GlobalTheory.exists_algEquiv_apply_eq_of_fixes_preimage_base | (intros; apply GlobalTheory.exists_algEquiv_apply_eq_of_fixes_preimage_base <;> assumption)
