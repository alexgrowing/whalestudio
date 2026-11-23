import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL3LiftedWhittaker
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
theorem _root_.GlobalTheory.T.temperedBoundGL3_lifted_whittaker : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ), LFS.Hyp ψ ν W' Φ → TemperedBoundGL3 (LFS.Wp ψ W' Φ) := by
  first | exact @GlobalTheory.CompanionTheory.LFTempered.temperedBoundGL3_of_lift | exact GlobalTheory.CompanionTheory.LFTempered.temperedBoundGL3_of_lift | (intros; apply GlobalTheory.CompanionTheory.LFTempered.temperedBoundGL3_of_lift <;> assumption)
