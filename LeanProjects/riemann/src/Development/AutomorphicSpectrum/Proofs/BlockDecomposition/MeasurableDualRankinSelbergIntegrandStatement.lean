import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableDualRankinSelbergIntegrand
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
theorem _root_.GlobalTheory.T.measurable_dual_rankin_selberg_integrand : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ), Continuous W → Measurable W' → Measurable (fun p : Fˣ × Fˣ × GL (Fin 2) F => GL2LocalData.dW3 W (GL2LocalData.em (dg2 (p.1 * p.2.1) p.2.1 * p.2.2)) * GL2LocalData.dW2 W' (dg2 (p.1 * p.2.1) p.2.1 * p.2.2)) := by
  first | exact @GlobalTheory.CompanionTheory.DualHol.IwMeas.measurable_dual_iwasawa | exact GlobalTheory.CompanionTheory.DualHol.IwMeas.measurable_dual_iwasawa | (intros; apply GlobalTheory.CompanionTheory.DualHol.IwMeas.measurable_dual_iwasawa <;> assumption)
