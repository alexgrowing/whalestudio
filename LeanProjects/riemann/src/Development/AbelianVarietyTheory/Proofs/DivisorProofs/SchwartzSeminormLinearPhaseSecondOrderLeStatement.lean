import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormLinearPhaseSecondOrderLe
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzSeminorm_linearPhase_second_order_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f) ≤ C * t ^ 2 := by
  first | exact @GlobalTheory.LinearPhase.seminorm_phase_sub_le | exact GlobalTheory.LinearPhase.seminorm_phase_sub_le | (intros; apply GlobalTheory.LinearPhase.seminorm_phase_sub_le <;> assumption)
