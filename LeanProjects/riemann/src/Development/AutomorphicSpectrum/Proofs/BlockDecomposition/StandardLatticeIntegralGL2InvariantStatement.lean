import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardLatticeIntegralGL2Invariant
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
theorem _root_.GlobalTheory.T.standard_lattice_integral_GL2_invariant : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (k : GL (Fin 2) F), k ∈ GLnLocal.integralGL F 2 → GlobalTheory.CompanionTheory.WS.lat0 F ∘ GlobalTheory.CompanionTheory.WS.rowAct k = GlobalTheory.CompanionTheory.WS.lat0 F := by
  first | exact @GlobalTheory.CompanionTheory.WS.standard_lattice_indicator_invariant | exact GlobalTheory.CompanionTheory.WS.standard_lattice_indicator_invariant | (intros; apply GlobalTheory.CompanionTheory.WS.standard_lattice_indicator_invariant <;> assumption)
