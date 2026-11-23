import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpanSetEqLatticePreimage
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
theorem _root_.GlobalTheory.T.span_set_eq_lattice_preimage : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F), ∃ h : GL (Fin 2) F, GlobalTheory.CompanionTheory.WS.spanSet n x = GlobalTheory.CompanionTheory.WS.rowAct h ⁻¹' GlobalTheory.CompanionTheory.WS.Ln F 0 := by
  first | exact @GlobalTheory.CompanionTheory.WS.spanSet_eq_preimage_Ln | exact GlobalTheory.CompanionTheory.WS.spanSet_eq_preimage_Ln | (intros; apply GlobalTheory.CompanionTheory.WS.spanSet_eq_preimage_Ln <;> assumption)
