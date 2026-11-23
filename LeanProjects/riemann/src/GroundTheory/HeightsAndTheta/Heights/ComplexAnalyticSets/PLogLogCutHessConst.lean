import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.CovLog
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogLogCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

theorem hessC_of_eventually_const {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} {c : ℝ}
    (h : φ =ᶠ[𝓝 y] fun _ => c) : hessC φ y = 0 ∧ hessC (fun z => φ z ^ 2 / 2) y = 0 := by
  have h2 : (fun z => φ z ^ 2 / 2) =ᶠ[𝓝 y] fun _ => c ^ 2 / 2 := by
    filter_upwards [h] with z hz
    rw [hz]
  have hc : ∀ a : ℝ, hessC (fun _ : Fin D → ℂ => a) y = 0 := by
    intro a
    ext i j
    simp [hessC]
  exact ⟨(hessC_congr' h).trans (hc c), (hessC_congr' h2).trans (hc _)⟩

theorem cutStep_of_one_le {s : ℝ} (hs : 1 ≤ s) : cutStep s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutStep_of_le_half {s : ℝ} (hs : s ≤ 1 / 2) : cutStep s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem continuousAt_normSq_eval {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) :
    ContinuousAt (fun z => ‖eval z Q‖ ^ 2) y :=
  ((AnalyticOnNhd.eval_mvPolynomial Q y (Set.mem_univ y)).continuousAt.norm).pow 2

theorem logLogCut_eventually_zero {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) {y : Fin m → ℂ}
    (hy : ‖eval y Q‖ ^ 2 < cutLevel k) : logLogCut Q k =ᶠ[𝓝 y] fun _ => 0 := by
  filter_upwards [(continuousAt_normSq_eval Q y).preimage_mem_nhds (Iio_mem_nhds hy)] with z hz
  have hz : ‖eval z Q‖ ^ 2 < cutLevel k := hz
  have hlt := (cutLevel_mem k).2
  unfold logLogCut
  split_ifs with h0 h1
  · rfl
  · linarith
  · have hw0 : 0 < ‖eval z Q‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have e1 : Real.log (‖eval z Q‖ ^ 2) < -Real.exp ((k : ℝ) + 1) :=
      (Real.log_lt_iff_lt_exp hw0).2 hz
    have e2 : (k : ℝ) + 1 < Real.log (-logAbsSq Q z) :=
      (Real.lt_log_iff_exp_lt (by rw [logAbsSq]; linarith [Real.exp_pos ((k : ℝ) + 1)])).2
        (by rw [logAbsSq]; linarith)
    apply cutStep_of_one_le
    rw [le_div_iff₀ (by positivity)]
    linarith

theorem logLogCut_eventually_one {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) {y : Fin m → ℂ}
    (hy : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < ‖eval y Q‖ ^ 2) :
    logLogCut Q k =ᶠ[𝓝 y] fun _ => 1 := by
  filter_upwards [(continuousAt_normSq_eval Q y).preimage_mem_nhds (Ioi_mem_nhds hy)] with z hz
  have hz : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < ‖eval z Q‖ ^ 2 := hz
  have hw0 : 0 < ‖eval z Q‖ ^ 2 := lt_trans (Real.exp_pos _) hz
  unfold logLogCut
  split_ifs with h0 h1
  · linarith
  · rfl
  · have hw1 : ‖eval z Q‖ ^ 2 < 1 := not_le.1 h1
    have e1 : -Real.exp (((k : ℝ) + 1) / 2) < Real.log (‖eval z Q‖ ^ 2) :=
      (Real.lt_log_iff_exp_lt hw0).2 hz
    have e0 : Real.log (‖eval z Q‖ ^ 2) < 0 := Real.log_neg hw0 hw1
    have e2 : Real.log (-logAbsSq Q z) < ((k : ℝ) + 1) / 2 :=
      (Real.log_lt_iff_lt_exp (by rw [logAbsSq]; linarith)).2 (by rw [logAbsSq]; linarith)
    apply cutStep_of_le_half
    rw [div_le_iff₀ (by positivity)]
    linarith

theorem logLogCut_eventually_step {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) {y : Fin m → ℂ}
    (h0 : 0 < ‖eval y Q‖ ^ 2) (h1 : ‖eval y Q‖ ^ 2 < 1) :
    logLogCut Q k =ᶠ[𝓝 y] fun z => cutStep (Real.log (-logAbsSq Q z) / ((k : ℝ) + 1)) := by
  filter_upwards [(continuousAt_normSq_eval Q y).preimage_mem_nhds (Ioo_mem_nhds h0 h1)] with z hz
  have hz : ‖eval z Q‖ ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := hz
  unfold logLogCut
  rw [if_neg hz.1.ne', if_neg (not_le.2 hz.2)]

end

end GroundTheory.Heights₂.Heights
