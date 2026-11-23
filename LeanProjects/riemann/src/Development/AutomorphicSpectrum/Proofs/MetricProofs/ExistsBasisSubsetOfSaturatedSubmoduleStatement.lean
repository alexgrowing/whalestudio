import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBasisSubsetOfSaturatedSubmodule
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientLatticeByIsotropicSubmoduleStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_subset_of_saturated_submodule : ∀ (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : Submodule ℤ Λ), (∀ (v : Λ) (n : ℤ), n ≠ 0 → n • v ∈ N → v ∈ N) → ∃ (k n : ℕ) (b : Module.Basis (Fin n) ℤ Λ) (f : Fin k → Fin n), Function.Injective f ∧ Submodule.span ℤ (Set.range fun i => b (f i)) = N := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lattice.exists_basis_span_eq_of_saturated | exact GlobalTheory.CompanionTheory.Ar.Lattice.exists_basis_span_eq_of_saturated | (intros; apply GlobalTheory.CompanionTheory.Ar.Lattice.exists_basis_span_eq_of_saturated <;> assumption)
