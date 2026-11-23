import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableModulusPowOnBoundedUnits
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_modulus_pow_on_bounded_units : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (δ B : ℝ), 0 < δ → Integrable (fun a : Fˣ => Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B} (fun a : Fˣ => (modulus (a : F) : ℝ) ^ δ) a) (multHaar F) := by
  first | exact @GlobalTheory.CompanionTheory.ModulusWeight.integrable_modulus_rpow_indicator | exact GlobalTheory.CompanionTheory.ModulusWeight.integrable_modulus_rpow_indicator | (intros; apply GlobalTheory.CompanionTheory.ModulusWeight.integrable_modulus_rpow_indicator <;> assumption)
