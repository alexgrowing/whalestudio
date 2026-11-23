import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetCharacterAverageVectorIndep
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_mirabolicDetCharacterAverage_vector_indep : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsClass ψ → ∀ (θ : (ZMod g)ˣ →* ℂˣ)
    (a : Fin (n + 1) → ZMod g), a ≠ 0 → ∀ b : Bool,
      tr (mirEl θ a b) ψ = tr (mirEl θ (if b then Pi.single 0 1 else Pi.single (Fin.last n) 1) b) ψ := by
  first | exact @GlobalTheory.MirAvg.tr_mirEl_indep | exact GlobalTheory.MirAvg.tr_mirEl_indep | (intros; apply GlobalTheory.MirAvg.tr_mirEl_indep <;> assumption)
