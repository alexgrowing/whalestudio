import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationKaehlerPrimeIdeal
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_kaehler_prime_ideal : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (σ σ' : Type)
    (r₀ : σ → Ω₀) (r₁ : σ' → Ω) (v : σ → σ'), (∀ p, algebraMap Ω₀ Ω (r₀ p) = r₁ (v p)) →
    ∀ (bd : Ideal (MvPolynomial σ ℤ)) (S : Subalgebra ℚ Ω₀) (S' : Subalgebra ℚ Ω) (θ : S →+* S'),
    (∀ s, ((θ s : S') : Ω) = algebraMap Ω₀ Ω s) → (∀ p, r₀ p ∈ S) → (∀ p, r₁ p ∈ S') →
    ∀ q : Ideal S',
    ((∀ g ∈ bd.map (MvPolynomial.rename v), ∀ s : S', (s : Ω) = MvPolynomial.aeval r₁ g → s ∈ q) ↔
      (∀ g ∈ bd, ∀ s : S, (s : Ω₀) = MvPolynomial.aeval r₀ g → s ∈ q.comap θ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BoundaryPull.vanishing_rename_iff | exact GlobalTheory.CompanionTheory.Ar.BoundaryPull.vanishing_rename_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.BoundaryPull.vanishing_rename_iff <;> assumption)
