import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnZetaGL3GL2Dual
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
theorem _root_.GlobalTheory.T.differentiableOn_zetaGL3GL2_dual : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ), TemperedBoundGL3 W → TemperedBoundGL2 W' → DifferentiableOn ℂ (fun u => GL2LocalData.zetaGL3GL2 ψ (GL2LocalData.dW3 W) (GL2LocalData.dW2 W') u) {u : ℂ | 0 < u.re} := by
  first | exact @GlobalTheory.CompanionTheory.DualHolo.holo | exact GlobalTheory.CompanionTheory.DualHolo.holo | (intros; apply GlobalTheory.CompanionTheory.DualHolo.holo <;> assumption)
