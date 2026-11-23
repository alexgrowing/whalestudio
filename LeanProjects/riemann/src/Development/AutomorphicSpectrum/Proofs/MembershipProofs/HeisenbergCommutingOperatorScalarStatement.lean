import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.HeisenbergCommutingOperatorScalar
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_heisenberg_translates_separate : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → ∀ Φ ∈ schA F κ, (∀ w, thetaSum F (schr ψ w Φ) = 0) → Φ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ThetaInj.theta_inj | exact GlobalTheory.CompanionTheory.ThetaInj.theta_inj | (intros; apply GlobalTheory.CompanionTheory.ThetaInj.theta_inj <;> assumption)
