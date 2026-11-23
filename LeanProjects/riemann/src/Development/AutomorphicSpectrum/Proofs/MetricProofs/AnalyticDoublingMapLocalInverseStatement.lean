import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticDoublingMapLocalInverse
import Mathlib
open Set Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_doubling_map_local_inverse : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b₀ : B) (d : B × V → V), AnalyticAt ℂ d (b₀, 0) → d (b₀, 0) = 0 → HasFDerivAt d ((2 : ℂ) • ContinuousLinearMap.snd ℂ B V) (b₀, 0) → ∃ h : B × V → V, AnalyticAt ℂ h (b₀, 0) ∧ h (b₀, 0) = 0 ∧ (∀ᶠ p : B × V in 𝓝 (b₀, 0), d (p.1, h p) = p.2) ∧ (∀ᶠ p : B × V in 𝓝 (b₀, 0), h (p.1, d p) = p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.FamilyInverse.exists_analytic_family_inverse | exact GlobalTheory.CompanionTheory.Metric.FamilyInverse.exists_analytic_family_inverse | (intros; apply GlobalTheory.CompanionTheory.Metric.FamilyInverse.exists_analytic_family_inverse <;> assumption)
