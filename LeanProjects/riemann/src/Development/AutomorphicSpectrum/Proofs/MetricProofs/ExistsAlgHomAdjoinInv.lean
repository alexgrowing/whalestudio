import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestAlt
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp.Kext

theorem exists_algHom_adjoin_inv :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ)
      (S : Subalgebra ℚ Ω) (E : Type) [CommRing E] [Algebra ℚ E] (u : σ → E),
      aeval τ F ≠ 0 → S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) →
      (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → aeval u G = 0) → IsUnit (aeval u F) →
      ∃ φ : S →ₐ[ℚ] E, ∀ (G : MvPolynomial σ ℚ) (s : S), (s : Ω) = aeval τ G →
        φ s = aeval u G :=
  _root_.UpperTheory.Reformulated.B.Yde9.main

end GlobalTheory.CompanionTheory.Ar.Cmp.Kext
