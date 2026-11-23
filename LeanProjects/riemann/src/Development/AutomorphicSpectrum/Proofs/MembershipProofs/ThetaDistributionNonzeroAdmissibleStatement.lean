import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissible
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_distribution_heisenberg_invariant : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → (∀ w, ∀ Φ ∈ schA F κ, schr ψ w Φ ∈ schA F κ) ∧ ∀ (w : (κ → F) × (κ → F)) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ), thetaSum F (schr ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (w.1 i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (w.2 i)) Φ) = thetaSum F Φ := by
  first | exact @GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum | exact GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum | (intros; apply GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum <;> assumption)
