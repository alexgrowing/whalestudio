import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2QuadraticWhittaker
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
theorem _root_.GlobalTheory.T.temperedBoundGL2_quadratic_whittaker : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ (lam : ℂ) (c : Eˣ →* ℂˣ), IsUnit1 c → ∀ Φ ∈ GL2LocalData.SBc F E c, ∀ h₀ : GL (Fin 2) F, TemperedBoundGL2 (fun g => GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) lam c Φ (g * h₀)) := by
  first | exact @GlobalTheory.CompanionTheory.WcB.temperedBoundGL2_compact_whittaker | exact GlobalTheory.CompanionTheory.WcB.temperedBoundGL2_compact_whittaker | (intros; apply GlobalTheory.CompanionTheory.WcB.temperedBoundGL2_compact_whittaker <;> assumption)
