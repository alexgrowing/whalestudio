import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatPlaneCosetSpan
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
theorem _root_.GlobalTheory.T.schwartz_bruhat_plane_coset_span : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (Ψ : F × F → ℂ), GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∃ (n : ℤ) (s : Finset (F × F)) (a : F × F → ℂ), Ψ = ∑ x ∈ s, a x • GlobalTheory.CompanionTheory.WS.cosetInd n x := by
  first | exact @GlobalTheory.CompanionTheory.WS.Decomp.exists_sum_cosetInd | exact GlobalTheory.CompanionTheory.WS.Decomp.exists_sum_cosetInd | (intros; apply GlobalTheory.CompanionTheory.WS.Decomp.exists_sum_cosetInd <;> assumption)
