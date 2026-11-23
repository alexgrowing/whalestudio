import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibility
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_distribution_nonzero_admissible : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ], (∀ Φ ∈ schA F κ, Summable fun x : κ → F => ‖Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (x i))‖) ∧ (∃ l ∈ (adeleClass F).adm κ, ∀ Φ ∈ schA F κ, l Φ = thetaSum F Φ) ∧ ∃ Φ ∈ schA F κ, thetaSum F Φ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ThetaAdm.theta_adm | exact GlobalTheory.CompanionTheory.ThetaAdm.theta_adm | (intros; apply GlobalTheory.CompanionTheory.ThetaAdm.theta_adm <;> assumption)
