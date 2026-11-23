import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartHatCoeffBounds
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_hat_coeff_bounds : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (t : ℂ), M.Chart ℓ → ¬ M.Small t → Bd 1 (hat M.ι ℓ (fun z => M.x (z + t))) ∧ Bd 1 (hat M.ι ℓ (fun z => M.y (z + t))) ∧ ∀ r : ℝ, r < 1 → ∃ n, 0 < n ∧ r < ‖coeff n (hat M.ι ℓ (fun z => M.x (z + t)))‖ := by
  first | exact @GlobalTheory.MomOne.Transl.translate_integral | exact GlobalTheory.MomOne.Transl.translate_integral | (intros; apply GlobalTheory.MomOne.Transl.translate_integral <;> assumption)
