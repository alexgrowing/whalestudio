import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationEmbeddingGeneratorEqOne
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_embedding_generator_eq_one' : ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime → (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal → ∀ (α : 𝓞 K) (h : ℕ), Ideal.span {α} = P.asIdeal ^ h → ∀ σ : K →+* ℂ, A.valuation (σ (α : K)) = 1 := by
  first | exact @GlobalTheory.valuation_embedding_generator_eq_one | exact GlobalTheory.valuation_embedding_generator_eq_one | (intros; apply GlobalTheory.valuation_embedding_generator_eq_one <;> assumption)
