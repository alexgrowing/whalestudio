import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIdealExtensionLocalDomain
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_ideal_extension_local_domain : ∀ (R B : Type) [CommRing R] [IsDedekindDomain R] [CommRing B] [IsDomain B] [IsNoetherianRing B] (u : R →+* B), u.FiniteType → (∀ p : Ideal R, p.IsMaximal → ∀ a b : B, a * b ∈ p.map u → a ∈ p.map u ∨ b ∈ p.map u) → ∀ (f : B) (d : R), d ≠ 0 → (∀ m : Ideal B, m.IsMaximal → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (ψ : B →+* O), (∀ b, b ∉ m → IsUnit (ψ b)) ∧ (∀ b ∈ m, ¬ IsUnit (ψ b)) ∧ Function.Injective (ψ.comp u) ∧ ∃ c, ψ f = ψ (u d) * c) → ∃ a, f = u d * a := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.RegularDvd.dvd_of_local | exact GlobalTheory.CompanionTheory.Ggeo.RegularDvd.dvd_of_local | (intros; apply GlobalTheory.CompanionTheory.Ggeo.RegularDvd.dvd_of_local <;> assumption)
