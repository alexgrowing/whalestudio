import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterAnnulusIntegral
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_character_annulus_integral : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (μ : Fˣ →* ℂˣ), IsUnramifiedChar μ → ∀ A D : ℤ, ∫ u : Fˣ, (if -A ≤ ord (u : F) ∧ ord (u : F) ≤ -D then ((μ u : ℂˣ) : ℂ) else 0) ∂multHaar F = ∑ j ∈ Finset.Icc D A, ((μ (unifUnit F) : ℂˣ) : ℂ) ^ (-j) := by
  first | exact @GlobalTheory.CompanionTheory.WS.integral_unramified_shells | exact GlobalTheory.CompanionTheory.WS.integral_unramified_shells | (intros; apply GlobalTheory.CompanionTheory.WS.integral_unramified_shells <;> assumption)
