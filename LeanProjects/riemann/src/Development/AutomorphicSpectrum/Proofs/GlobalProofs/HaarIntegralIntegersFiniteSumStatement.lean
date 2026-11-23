import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HaarIntegralIntegersFiniteSum
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_integral_integers_finite_sum : ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (g : v.adicCompletion E → ℂ), (∀ y, 1 < Valued.v y → g y = 0) → (∀ y h : v.adicCompletion E, Valued.v h ≤ WithZero.exp (-(m : ℤ)) → g (y + h) = g y) → ∫ y, g y ∂haarIntegers (v.adicCompletion E) = (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℂ))⁻¹ * ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, g (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) := by
  first | exact @GlobalTheory.CompanionTheory.PeriodicInt.integral_eq_finsum | exact GlobalTheory.CompanionTheory.PeriodicInt.integral_eq_finsum | (intros; apply GlobalTheory.CompanionTheory.PeriodicInt.integral_eq_finsum <;> assumption)
