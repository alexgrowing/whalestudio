import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexLinearExtensionOfTraceIsometry
import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexLinear_extension_of_traceIsometry' : ∀ (K E : Type) [Field K] [Field E] [Algebra K E] (cj : E → E) (ι : Type) [Fintype ι] (φ : E →+* ℂ) (emb : ι → E →+* ℂ), (∀ y, φ (cj y) = starRingEnd ℂ (φ y)) → (∀ τ y, emb τ (cj y) = starRingEnd ℂ (emb τ y)) → (∀ τ (x : K), emb τ (algebraMap K E x) = φ (algebraMap K E x)) → (∀ y, ∑ τ, emb τ y = φ (algebraMap K E (Algebra.trace K E y))) → ∀ γ : IsoKG K E cj ι, ∃ gC : (Fin 4 × ι → ℂ) ≃ₗ[ℂ] (Fin 4 × ι → ℂ), ∀ x : Fin 4 → E, gC (fun w => emb w.2 (x w.1)) = fun w => φ (algebraMap K E (γ.g x w)) := by
  first | exact @GlobalTheory.exists_complexLinear_extension_of_traceIsometry | exact GlobalTheory.exists_complexLinear_extension_of_traceIsometry | (intros; apply GlobalTheory.exists_complexLinear_extension_of_traceIsometry <;> assumption)
