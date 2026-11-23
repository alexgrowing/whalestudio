import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerLowerLeftNonzero
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
theorem _root_.GlobalTheory.T.weil_whittaker_lower_left_nonzero : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → ∀ g : GL (Fin 2) F, g.val 1 0 ≠ 0 → ∀ u : Fˣ, GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) = mp u 1 * GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.pF χ Φ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) u := by
  first | exact @GlobalTheory.CompanionTheory.WS.model_ne | exact GlobalTheory.CompanionTheory.WS.model_ne | (intros; apply GlobalTheory.CompanionTheory.WS.model_ne <;> assumption)
