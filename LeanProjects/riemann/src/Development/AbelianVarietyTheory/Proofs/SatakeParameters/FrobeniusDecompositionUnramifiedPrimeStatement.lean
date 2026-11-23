import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusDecompositionUnramifiedPrime
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_decomposition_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ), p.Prime → Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(p : ℤ)}) → ∃ (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal ∧ ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 ∧ (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) ∧ Nat.card (𝓞 E ⧸ Q.asIdeal) = p ^ orderOf φ ∧ (∀ g : E ≃ₐ[ℚ] E, (∀ x : 𝓞 E, g • x ∈ Q.asIdeal ↔ x ∈ Q.asIdeal) ↔ g ∈ Subgroup.zpowers φ) ∧ ∀ Q' : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ Q'.asIdeal → ∃ g : E ≃ₐ[ℚ] E, ∀ x : 𝓞 E, x ∈ Q'.asIdeal ↔ g • x ∈ Q.asIdeal := by
  first | exact @GlobalTheory.UnramifiedFrobenius.exists_frobenius | exact GlobalTheory.UnramifiedFrobenius.exists_frobenius | (intros; apply GlobalTheory.UnramifiedFrobenius.exists_frobenius <;> assumption)
