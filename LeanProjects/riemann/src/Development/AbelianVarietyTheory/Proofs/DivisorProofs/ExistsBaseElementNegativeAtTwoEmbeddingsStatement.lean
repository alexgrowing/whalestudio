import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementNegativeAtTwoEmbeddings
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalIffEtaProd
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_element_negative_at_two_embeddings : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L], Module.finrank K L = 2 → ∀ σ : L →+* L, σ ≠ RingHom.id L → (∀ x : K, σ (algebraMap K L x) = algebraMap K L x) → (∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ ε ε' : L →+* ℂ, ε ≠ ε' → ε ≠ ComplexEmbedding.conjugate ε' → ∃ h : K, h ≠ 0 ∧ (ε (algebraMap K L h)).re < 0 ∧ (ε' (algebraMap K L h)).re < 0 ∧ (∀ φ : L →+* ℂ, φ ≠ ε → φ ≠ ComplexEmbedding.conjugate ε → φ ≠ ε' → φ ≠ ComplexEmbedding.conjugate ε' → 0 < (φ (algebraMap K L h)).re) ∧ ∀ v : HeightOneSpectrum (𝓞 K), ∃ z : v.adicCompletion K ⊗[K] L, Algebra.norm (v.adicCompletion K) z = algebraMap K (v.adicCompletion K) h := by
  first | (exact @GlobalTheory.QuadSigns.exists_signs) | (exact GlobalTheory.QuadSigns.exists_signs) | (intros; apply GlobalTheory.QuadSigns.exists_signs  <;> assumption)
