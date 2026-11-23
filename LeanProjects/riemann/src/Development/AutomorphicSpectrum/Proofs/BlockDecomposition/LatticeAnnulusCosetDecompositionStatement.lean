import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeAnnulusCosetDecomposition
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
theorem _root_.GlobalTheory.T.lattice_annulus_coset_decomposition : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F), x ∉ GlobalTheory.CompanionTheory.WS.Ln F n → ∃ s : Finset Fˣ, s.Nonempty ∧ (∀ t ∈ s, t ∈ unitFiltrationUnits F 0) ∧ (GlobalTheory.CompanionTheory.WS.spanSet n x).indicator (1 : F × F → ℂ) - (GlobalTheory.CompanionTheory.WS.spanSet n (((unifUnit F : Fˣ) : F) • x)).indicator (1 : F × F → ℂ) = ∑ t ∈ s, GlobalTheory.CompanionTheory.WS.cosetInd n ((t : F) • x) := by
  first | exact @GlobalTheory.CompanionTheory.WS.Orbit.main | exact GlobalTheory.CompanionTheory.WS.Orbit.main | (intros; apply GlobalTheory.CompanionTheory.WS.Orbit.main <;> assumption)
