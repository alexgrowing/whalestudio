import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrFrobeniusLift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_frobenius_lift : ∀ (E : Type) [Field E] [NumberField E] (p n : ℕ) (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), p.Prime → ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal → ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 → (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) → φ ^ n = 1 → ∃ (W Qq : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Field Qq) (_ : Algebra W Qq) (i : E →+* Qq) (σ : Qq ≃+* Qq), IsFractionRing W Qq ∧ Irreducible (p : W) ∧ Nat.card (W ⧸ Ideal.span {(p : W)}) = Nat.card (𝓞 E ⧸ Q.asIdeal) ∧ IsAdicComplete (Ideal.span {(p : W)}) W ∧ (∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)) ∧ σ ^ n = 1 ∧ (∀ x : E, σ (i x) = i (φ x)) ∧ (∀ x : E, Formalism.L2.Col.IntAt Q x ↔ i x ∈ Set.range (algebraMap W Qq)) ∧ ∀ (y : W) (k : ℕ), ∃ (x : 𝓞 E) (z : W), i (x : E) = algebraMap W Qq (y + (p : W) ^ k * z) := by
  first | exact @GlobalTheory.UnramCompletion.exists_completion_frobenius | exact GlobalTheory.UnramCompletion.exists_completion_frobenius | (intros; apply GlobalTheory.UnramCompletion.exists_completion_frobenius <;> assumption)
