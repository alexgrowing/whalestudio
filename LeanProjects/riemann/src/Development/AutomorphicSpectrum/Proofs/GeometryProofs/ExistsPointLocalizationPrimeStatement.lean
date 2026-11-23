import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPointLocalizationPrime
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_localization_prime : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (p : Cpt ξ) (I : Ideal (regAt ξ p)), I.IsPrime → ∃ q : Cpt ξ, q.1 ⤳ p.1 ∧ ∀ a : Ω, a ∈ regAt ξ q ↔ ∃ s : regAt ξ p, s ∉ I ∧ (s : Ω) * a ∈ regAt ξ p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.regAt_prime_generisation | exact GlobalTheory.CompanionTheory.Ar.regAt_prime_generisation | (intros; apply GlobalTheory.CompanionTheory.Ar.regAt_prime_generisation <;> assumption)
