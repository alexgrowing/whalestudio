import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2OfInduced
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
theorem _root_.GlobalTheory.T.temperedBoundGL2_of_induced : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (V : Submodule ℂ (GL (Fin 2) F → ℂ)), IsUnit1 μ₁ → IsUnit1 μ₂ → WhittakerModelGL2 ψ μ₁ μ₂ V → ∀ W ∈ V, TemperedBoundGL2 W := by
  first | exact @GlobalTheory.CompanionTheory.DualHol.temperedBoundGL2_of_whittaker | exact GlobalTheory.CompanionTheory.DualHol.temperedBoundGL2_of_whittaker | (intros; apply GlobalTheory.CompanionTheory.DualHol.temperedBoundGL2_of_whittaker <;> assumption)
