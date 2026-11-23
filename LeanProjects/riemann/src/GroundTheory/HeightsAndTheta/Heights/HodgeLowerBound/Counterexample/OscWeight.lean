import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Taut

def cutoff (x : ℝ) : ℝ := Real.smoothTransition (2 - 8 * x)

def oscS (u : ℂ) : ℝ := Real.sin ((-1 / 2) * Real.log (‖u‖ ^ 2))

def oscW (u : ℂ) : ℝ := cutoff (‖u‖ ^ 2) * oscS u

theorem contDiff_cutoffN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun u : ℂ => cutoff (‖u‖ ^ 2) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  exact h1.comp ((contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ))))

theorem contDiffAt_oscS {u : ℂ} (hu : u ≠ 0) : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) oscS u := by
  have hne : ‖u‖ ^ 2 ≠ 0 := by positivity
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℂ => Real.log (‖v‖ ^ 2)) u :=
    (contDiff_norm_sq ℝ).contDiffAt.log hne
  exact Real.contDiff_sin.contDiffAt.comp u (contDiffAt_const.mul h1)

theorem contDiffAt_oscW {u : ℂ} (hu : u ≠ 0) : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) oscW u :=
  contDiff_cutoffN.contDiffAt.mul (contDiffAt_oscS hu)

end GroundTheory.Heights₂.Heights.LowerBoundFree.Taut
