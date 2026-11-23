import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsOfCZero
open MeasureTheory Finset GlobalTheory.Chamber
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Chamber

variable {k : ℕ}

theorem gamP_ne_zero_wt_mul_rt_nonpos {P R : Finset (SV k)} {Y H : A0 k} (hg : gamP P R Y H ≠ 0) {u : SV k}
    (hu : u ∈ P \ R) : ⟪wt R u, H - Y⟫_ℝ * ⟪rt P u, H⟫_ℝ ≤ 0 := by
  have huP := (mem_sdiff.1 hu).1
  have huR := (mem_sdiff.1 hu).2
  by_cases hr : 0 < ⟪rt P u, H⟫_ℝ
  · refine mul_nonpos_of_nonpos_of_nonneg ?_ hr.le
    by_contra hd
    push_neg at hd
    apply hg
    have hpair : ∀ S : Finset (SV k), u ∉ S →
        (-1 : ℝ) ^ (insert u S \ R).card * tau P (insert u S) H * tauHat (insert u S) R (H - Y)
          = -((-1) ^ (S \ R).card * tau P S H * tauHat S R (H - Y)) := by
      intro S huS
      have e1 : insert u S \ R = insert u (S \ R) := Finset.insert_sdiff_of_notMem _ huR
      have hn : u ∉ S \ R := fun h => huS (mem_sdiff.1 h).1
      have i2 : (∀ v ∈ P \ insert u S, 0 < ⟪rt P v, H⟫_ℝ) ↔ (∀ v ∈ P \ S, 0 < ⟪rt P v, H⟫_ℝ) := by
        constructor
        · intro h v hv
          by_cases hvu : v = u
          · subst hvu; exact hr
          · exact h v (mem_sdiff.2 ⟨(mem_sdiff.1 hv).1, fun h' => (mem_insert.1 h').elim hvu (mem_sdiff.1 hv).2⟩)
        · intro h v hv
          exact h v (mem_sdiff.2 ⟨(mem_sdiff.1 hv).1, fun h' => (mem_sdiff.1 hv).2 (mem_insert_of_mem h')⟩)
      have e2 : tau P (insert u S) H = tau P S H := by
        unfold tau; exact if_congr i2 rfl rfl
      have i3 : (∀ v ∈ insert u S \ R, 0 < ⟪wt R v, H - Y⟫_ℝ) ↔ (∀ v ∈ S \ R, 0 < ⟪wt R v, H - Y⟫_ℝ) := by
        rw [e1, forall_mem_insert]
        exact ⟨fun h => h.2, fun h => ⟨hd, h⟩⟩
      have e3 : tauHat (insert u S) R (H - Y) = tauHat S R (H - Y) := by
        unfold tauHat; exact if_congr i3 rfl rfl
      rw [e1, card_insert_of_notMem hn, pow_succ, e2, e3]
      ring
    unfold gamP
    refine Finset.sum_involution (fun S _ => if u ∈ S then S.erase u else insert u S) ?_ ?_ ?_ ?_
    · intro S hS
      by_cases huS : u ∈ S
      · simp only [huS, if_true]
        have := hpair (S.erase u) (notMem_erase u S)
        rw [insert_erase huS] at this
        rw [this]; ring
      · simp only [huS, if_false]
        rw [hpair S huS]; ring
    · intro S hS _
      by_cases huS : u ∈ S
      · simp only [huS, if_true]; exact fun h => notMem_erase u S (by rw [h]; exact huS)
      · simp only [huS, if_false]; exact fun h => huS (h ▸ mem_insert_self u S)
    · intro S hS
      simp only [between, mem_filter, mem_powerset] at hS ⊢
      by_cases huS : u ∈ S
      · simp only [huS, if_true]
        exact ⟨(erase_subset u S).trans hS.1, fun v hv => mem_erase.2 ⟨fun e => huR (e ▸ hv), hS.2 hv⟩⟩
      · simp only [huS, if_false]
        exact ⟨insert_subset huP hS.1, hS.2.trans (subset_insert u S)⟩
    · intro S hS
      by_cases huS : u ∈ S
      · simp only [huS, if_true, notMem_erase, if_false]; exact insert_erase huS
      · simp only [huS, if_false, mem_insert_self, if_true]; exact erase_insert huS
  · push_neg at hr
    refine mul_nonpos_of_nonneg_of_nonpos ?_ hr
    by_contra hd
    push_neg at hd
    apply hg
    unfold gamP
    refine Finset.sum_eq_zero fun S hS => ?_
    by_cases huS : u ∈ S
    · have : tauHat S R (H - Y) = 0 := if_neg fun h => lt_asymm (h u (mem_sdiff.2 ⟨huS, huR⟩)) hd
      rw [this, mul_zero]
    · have : tau P S H = 0 := if_neg fun h => not_lt.2 hr (h u (mem_sdiff.2 ⟨huP, huS⟩))
      rw [this, mul_zero, zero_mul]

theorem gamP_bounded_support : ∀ (k : ℕ) (P R : Finset (SV k)) (Y : A0 k), IsPar P → R ⊆ P →
    ∃ C : ℝ, ∀ H ∈ aMQ (aP P) R, gamP P R Y H ≠ 0 → ‖H‖ ≤ C := by
  intro k P R Y hP hRP
  have hpr : ∀ (Q : Finset (SV k)) (v : A0 k), pr Q v ∈ aP Q := fun Q v => Submodule.starProjection_apply_mem _ _
  have hwtp : ∀ (Q : Finset (SV k)) (v : SV k), wt Q v ∈ (aP Q)ᗮ := fun Q v =>
    Submodule.sub_starProjection_mem_orthogonal _
  have hsp : ∀ (Q : Finset (SV k)) (w : SV k), w ∈ Q → vec w ∈ aP Q := fun Q w hw =>
    Submodule.subset_span ⟨w, hw, rfl⟩
  have hrtmem : ∀ u ∈ P, rt P u ∈ aP P := fun u hu =>
    sub_mem (hsp P u hu) (vecSpan_mono (erase_subset u P) (hpr _ _))
  have horth : ∀ u ∈ P, ∀ w ∈ P, w ≠ u → ⟪vec w, rt P u⟫_ℝ = 0 := fun u _ w hw hwu =>
    Submodule.inner_right_of_mem_orthogonal (hsp _ w (mem_erase.2 ⟨hwu, hw⟩)) (hwtp _ _)
  have hpos : ∀ u ∈ P, 0 < ⟪vec u, rt P u⟫_ℝ := fun u hu => by
    have hne : rt P u ≠ 0 := hP.wt_ne_zero (erase_subset u P) (by simp [hu])
    have h0 : ⟪pr (P.erase u) (vec u), rt P u⟫_ℝ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hpr _ _) (hwtp _ _)
    have e : ⟪vec u, rt P u⟫_ℝ = ⟪rt P u, rt P u⟫_ℝ := by
      calc ⟪vec u, rt P u⟫_ℝ = ⟪rt P u + pr (P.erase u) (vec u), rt P u⟫_ℝ := by rw [rt, wt, sub_add_cancel]
        _ = _ := by rw [inner_add_left, h0, add_zero]
    rw [e, real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.2 hne) 2
  refine ⟨∑ u ∈ P \ R, |⟪wt R u, Y⟫_ℝ| / ⟪vec u, rt P u⟫_ℝ * ‖rt P u‖, fun H hH hg => ?_⟩
  simp only [aMQ, Submodule.mem_inf] at hH
  obtain ⟨hHP, hHR⟩ := hH
  have hwt : ∀ u, ⟪wt R u, H⟫_ℝ = ⟪vec u, H⟫_ℝ := fun u => by
    rw [wt, inner_sub_left, Submodule.inner_right_of_mem_orthogonal (hpr R (vec u)) hHR, sub_zero]
  have hexp : H = ∑ u ∈ P \ R, (⟪vec u, H⟫_ℝ / ⟪vec u, rt P u⟫_ℝ) • rt P u := by
    set H' := H - ∑ u ∈ P \ R, (⟪vec u, H⟫_ℝ / ⟪vec u, rt P u⟫_ℝ) • rt P u with hH'
    have hm : H' ∈ aP P :=
      sub_mem hHP (sum_mem fun u hu => Submodule.smul_mem _ _ (hrtmem u (mem_sdiff.1 hu).1))
    have hv : ∀ w ∈ P, ⟪vec w, H'⟫_ℝ = 0 := by
      intro w hw
      rw [hH', inner_sub_right, inner_sum]
      simp_rw [real_inner_smul_right]
      by_cases hwR : w ∈ R
      · rw [Submodule.inner_right_of_mem_orthogonal (hsp R w hwR) hHR]
        rw [sum_eq_zero fun u hu => by
          rw [horth u (mem_sdiff.1 hu).1 w hw (fun e => (mem_sdiff.1 hu).2 (e ▸ hwR)), mul_zero]]
        simp
      · have hwPR : w ∈ P \ R := mem_sdiff.2 ⟨hw, hwR⟩
        rw [sum_eq_single w (fun u hu hne => by rw [horth u (mem_sdiff.1 hu).1 w hw hne.symm, mul_zero])
          (fun h => absurd hwPR h)]
        rw [div_mul_cancel₀ _ (hpos w hw).ne', sub_self]
    have hle : aP P ≤ (ℝ ∙ H')ᗮ := Submodule.span_le.2 (by
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
      exact hv w hw)
    have h2 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hm)
    exact sub_eq_zero.1 (inner_self_eq_zero.1 h2)
  have hsq : ‖H‖ ^ 2 = ∑ u ∈ P \ R, ⟪vec u, H⟫_ℝ / ⟪vec u, rt P u⟫_ℝ * ⟪rt P u, H⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    calc ⟪H, H⟫_ℝ = ⟪∑ u ∈ P \ R, (⟪vec u, H⟫_ℝ / ⟪vec u, rt P u⟫_ℝ) • rt P u, H⟫_ℝ :=
          congrArg (fun x => ⟪x, H⟫_ℝ) hexp
      _ = _ := by rw [sum_inner]; simp_rw [real_inner_smul_left]
  have hterm : ∀ u ∈ P \ R, ⟪vec u, H⟫_ℝ / ⟪vec u, rt P u⟫_ℝ * ⟪rt P u, H⟫_ℝ
      ≤ |⟪wt R u, Y⟫_ℝ| / ⟪vec u, rt P u⟫_ℝ * ‖rt P u‖ * ‖H‖ := by
    intro u hu
    have hs := gamP_ne_zero_wt_mul_rt_nonpos hg hu
    rw [inner_sub_right, hwt u] at hs
    have hn := hpos u (mem_sdiff.1 hu).1
    have h1 : ⟪vec u, H⟫_ℝ * ⟪rt P u, H⟫_ℝ ≤ ⟪wt R u, Y⟫_ℝ * ⟪rt P u, H⟫_ℝ := by
      rw [sub_mul] at hs; linarith
    have h2 : ⟪wt R u, Y⟫_ℝ * ⟪rt P u, H⟫_ℝ ≤ |⟪wt R u, Y⟫_ℝ| * (‖rt P u‖ * ‖H‖) :=
      calc _ ≤ |⟪wt R u, Y⟫_ℝ * ⟪rt P u, H⟫_ℝ| := le_abs_self _
        _ = |⟪wt R u, Y⟫_ℝ| * |⟪rt P u, H⟫_ℝ| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
    calc ⟪vec u, H⟫_ℝ / ⟪vec u, rt P u⟫_ℝ * ⟪rt P u, H⟫_ℝ
        = (⟪vec u, H⟫_ℝ * ⟪rt P u, H⟫_ℝ) / ⟪vec u, rt P u⟫_ℝ := by ring
      _ ≤ (|⟪wt R u, Y⟫_ℝ| * (‖rt P u‖ * ‖H‖)) / ⟪vec u, rt P u⟫_ℝ :=
          div_le_div_of_nonneg_right (h1.trans h2) hn.le
      _ = _ := by ring
  have hC : 0 ≤ ∑ u ∈ P \ R, |⟪wt R u, Y⟫_ℝ| / ⟪vec u, rt P u⟫_ℝ * ‖rt P u‖ :=
    sum_nonneg fun u hu => mul_nonneg (div_nonneg (abs_nonneg _) (hpos u (mem_sdiff.1 hu).1).le) (norm_nonneg _)
  have hb : ‖H‖ * ‖H‖ ≤ (∑ u ∈ P \ R, |⟪wt R u, Y⟫_ℝ| / ⟪vec u, rt P u⟫_ℝ * ‖rt P u‖) * ‖H‖ := by
    rw [← sq, hsq, sum_mul]
    exact sum_le_sum hterm
  rcases (norm_nonneg H).eq_or_lt with h0 | h0
  · rw [← h0]; exact hC
  · exact le_of_mul_le_mul_right hb h0

end GlobalTheory.Chamber

end
