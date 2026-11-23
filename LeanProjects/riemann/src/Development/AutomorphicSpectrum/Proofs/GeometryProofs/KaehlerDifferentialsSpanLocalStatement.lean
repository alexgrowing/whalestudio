import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerDifferentialsSpanLocal
import Mathlib
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_differentials_span_local : ∀ (S B : Type) [CommRing S] [Algebra ℚ S] [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [Algebra ℂ B] (ψ : S →+* B) (φ : S →+* ℂ),
    (∀ s, ψ s - algebraMap ℂ B (φ s) ∈ IsLocalRing.maximalIdeal B) →
    ∀ (T : Set S), IsLocalRing.maximalIdeal B = Ideal.span ((fun s => ψ s - algebraMap ℂ B (φ s)) '' T) →
    ∀ (n : ℕ) (z : Fin n → S),
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    IsLocalRing.maximalIdeal B = Ideal.span (Set.range fun i => ψ (z i) - algebraMap ℂ B (φ (z i))) := by
  first | exact @GlobalTheory.CompanionTheory.Kaehler.maximalIdeal_eq_span_of_span_D | exact GlobalTheory.CompanionTheory.Kaehler.maximalIdeal_eq_span_of_span_D | (intros; apply GlobalTheory.CompanionTheory.Kaehler.maximalIdeal_eq_span_of_span_D <;> assumption)
