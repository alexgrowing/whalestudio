import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemSpanOfRealCombinationPeriods
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientLatticeByIsotropicSubmoduleStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_of_real_combination_periods : ∀ (g k n : ℕ) (Λ : Type) [AddCommGroup Λ] (P : Λ →+ (Fin g → ℂ)) (b : Module.Basis (Fin n) ℤ Λ) (f : Fin k → Fin n), LinearIndependent ℝ (fun j => P (b j)) → Function.Injective f → ∀ (x : Λ) (c : Fin k → ℝ), P x = ∑ i, (c i : ℂ) • P (b (f i)) → x ∈ Submodule.span ℤ (Set.range fun i => b (f i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.mem_span_part_of_period_real_comb | exact GlobalTheory.CompanionTheory.Ar.Cusp.mem_span_part_of_period_real_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.mem_span_part_of_period_real_comb <;> assumption)
