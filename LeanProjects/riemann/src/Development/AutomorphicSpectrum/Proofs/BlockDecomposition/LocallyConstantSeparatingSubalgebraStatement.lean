import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantSeparatingSubalgebra
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import GroundTheory.AutomorphicForms.MacdonaldWhittaker
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_constant_separating_subalgebra : ∀ (B : Type) [TopologicalSpace B] [CompactSpace B] (V : Submodule ℂ (B → ℂ)), (1 : B → ℂ) ∈ V → (∀ f ∈ V, ∀ g ∈ V, f * g ∈ V) → (∀ f ∈ V, IsLocallyConstant f) → ∀ Φ : B → ℂ, IsLocallyConstant Φ → (∀ p q, Φ p ≠ Φ q → ∃ f ∈ V, f p ≠ f q) → Φ ∈ V := by
  first | exact @GlobalTheory.CompanionTheory.LocConstSW.mem_of_separates | exact GlobalTheory.CompanionTheory.LocConstSW.mem_of_separates | (intros; apply GlobalTheory.CompanionTheory.LocConstSW.mem_of_separates <;> assumption)
