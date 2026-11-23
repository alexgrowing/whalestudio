import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumeratorIdealOfAntiInvariantDivisor
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numeratorIdeal_of_antiInvariant_divisor : ∀ (E : Type) [Field E] [NumberField E] (σ : 𝓞 E ≃+* 𝓞 E) (cp : HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 E)), (∀ x, σ (σ x) = x) → (∀ Q x, x ∈ (cp Q).asIdeal ↔ σ x ∈ Q.asIdeal) → ∀ δ : HeightOneSpectrum (𝓞 E) → ℤ, (Function.support δ).Finite → (∀ Q, δ (cp Q) = -δ Q) → ∃ cc : Ideal (𝓞 E), cc ≠ ⊥ ∧ cc ⊔ cc.map (σ : 𝓞 E →+* 𝓞 E) = ⊤ ∧ (∀ Q, FractionalIdeal.count E Q (cc : FractionalIdeal (𝓞 E)⁰ E) = max (δ Q) 0) ∧ (∀ b : 𝓞 E, (∀ Q, δ Q ≠ 0 → b ∉ Q.asIdeal) → cc ⊔ Ideal.span {b} = ⊤) ∧ ∀ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ WithZero.exp (-δ Q)) → J * idlE (cc.map (σ : 𝓞 E →+* 𝓞 E)) = idlE cc := by
  first | exact @GlobalTheory.NumeratorIdeal.exists_numerator | exact GlobalTheory.NumeratorIdeal.exists_numerator | (intros; apply GlobalTheory.NumeratorIdeal.exists_numerator <;> assumption)
