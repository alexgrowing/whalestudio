import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DoublingLimitLocalLogarithm
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IterDifferentiableOn
open Set Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_limit_local_logarithm : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b₀ : B) (h : B × V → V) (ρ C : ℝ), 0 < ρ → 0 ≤ C → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2) → ∃ L : B × V → V, TendstoUniformlyOn (fun (k : ℕ) (p : B × V) => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k p) L atTop (ball b₀ ρ ×ˢ ball (0 : V) ρ) ∧ ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖L (b, s) - s‖ ≤ 4 * C * ‖s‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit | exact GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit <;> assumption)
