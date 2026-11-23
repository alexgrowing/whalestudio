import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianTemperateGrowth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open GlobalTheory.ArchSch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_temperate_growth : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : LinearMap.BilinForm ℝ V)
    (L : V →ₗ[ℝ] ℝ) (c : ℝ), Function.HasTemperateGrowth (fun x : V => ech (Q x x + L x + c)) := by
  first | exact @GlobalTheory.QuadPhase.hasTemperateGrowth_quadPhase | exact GlobalTheory.QuadPhase.hasTemperateGrowth_quadPhase | (intros; apply GlobalTheory.QuadPhase.hasTemperateGrowth_quadPhase <;> assumption)
