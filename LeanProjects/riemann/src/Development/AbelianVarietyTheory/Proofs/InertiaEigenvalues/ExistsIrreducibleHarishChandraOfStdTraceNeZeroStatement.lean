import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleHarishChandraOfStdTraceNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_harishChandra_of_stdTrace_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (r a c : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (ψ : GlobalTheory.GLq.Gn p r → ℂ), r = a + 1 + c → GlobalTheory.GLq.IsChar ψ → stdTrace a θ ψ ≠ 0 → ∃ (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ) (β : GlobalTheory.GLq.Gn p c → ℂ), GlobalTheory.GLq.IsIrr α ∧ GlobalTheory.GLq.IsIrr β ∧ GlobalTheory.GLq.ip ψ (GlobalTheory.GLq.hc (a + 1) c α β r) ≠ 0 ∧ stdTrace a θ α ≠ 0 := by
  first | exact @GlobalTheory.LevelType.exists_irr_hc_of_stdTrace_ne_zero | exact GlobalTheory.LevelType.exists_irr_hc_of_stdTrace_ne_zero | (intros; apply GlobalTheory.LevelType.exists_irr_hc_of_stdTrace_ne_zero <;> assumption)
