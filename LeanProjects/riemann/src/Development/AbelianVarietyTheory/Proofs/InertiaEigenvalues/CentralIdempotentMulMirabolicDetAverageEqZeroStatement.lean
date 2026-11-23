import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentMulMirabolicDetAverageEqZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralIdempotent_mul_mirabolicDetAverage_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (r : ℕ) (ψ : Gn g r → ℂ), IsIrr ψ → ∀ (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g)
    (b : Bool), tr (mirEl θ a b) ψ = 0 → zOf ψ * mirEl θ a b = 0 := by
  first | exact @GlobalTheory.MirAvg.zOf_mul_mirEl_eq_zero | exact GlobalTheory.MirAvg.zOf_mul_mirEl_eq_zero | (intros; apply GlobalTheory.MirAvg.zOf_mul_mirEl_eq_zero <;> assumption)
