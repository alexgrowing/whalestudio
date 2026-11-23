import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.FamClosed

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasDerivAt_flow {R : ℝ → (E →L[ℂ] E)} (hR : ∀ s t, R (s + t) = (R s).comp (R t)) {a b : E}
    (h : HasDerivAt (fun t : ℝ => R t a) b 0) (s : ℝ) : HasDerivAt (fun t : ℝ => R t a) (R s b) s := by
  have h1 := ((R s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = R s (R (t - s) a)
  rw [← ContinuousLinearMap.comp_apply, ← hR, add_sub_cancel]

theorem norm_sub_le {f f' : ℝ → E} (hf : ∀ s, HasDerivAt f (f' s) s) {t C : ℝ}
    (hC : ∀ s, |s| ≤ |t| → ‖f' s‖ ≤ C) : ‖f t - f 0‖ ≤ C * |t| := by
  have := (convex_closedBall (0 : ℝ) |t|).norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := f') (C := C)
    (fun s _ => (hf s).hasDerivWithinAt) (fun s hs => hC s (by simpa using hs))
    (Metric.mem_closedBall_self (abs_nonneg t)) (y := t) (by simp)
  simpa using this

theorem taylor_bound {R : ℝ → (E →L[ℂ] E)} (h0 : R 0 = 1) (hR : ∀ s t, R (s + t) = (R s).comp (R t)) {M : ℝ}
    (hM : ∀ s, |s| ≤ 1 → ‖R s‖ ≤ M) {a b c : E} (ha : HasDerivAt (fun t : ℝ => R t a) b 0)
    (hb : HasDerivAt (fun t : ℝ => R t b) c 0) {t : ℝ} (ht : |t| ≤ 1) :
    ‖R t a - a - t • b‖ ≤ M * ‖c‖ * |t| * |t| := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have h1 : ∀ s, |s| ≤ |t| → ‖R s b - b‖ ≤ M * ‖c‖ * |t| := fun s hs => by
    have := norm_sub_le (hasDerivAt_flow hR hb) (t := s) (C := M * ‖c‖) fun u hu =>
      ((R u).le_opNorm c).trans (mul_le_mul_of_nonneg_right (hM u (hu.trans (hs.trans ht))) (norm_nonneg _))
    simp only [h0, ContinuousLinearMap.one_apply] at this
    exact this.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  have h2 := norm_sub_le (f := fun s : ℝ => R s a - s • b) (f' := fun s => R s b - b)
    (fun s => by
      have := (hasDerivAt_flow hR ha s).fun_sub ((hasDerivAt_id' s).smul_const b)
      rwa [one_smul] at this) h1
  simp only [h0, ContinuousLinearMap.one_apply, zero_smul, sub_zero] at h2
  rwa [sub_right_comm]

theorem hasDerivAt_of_bound {f : ℝ → E} {b : E} {K : ℝ}
    (h : ∀ t, |t| ≤ 1 → ‖f t - f 0 - t • b‖ ≤ K * |t| * |t|) : HasDerivAt f b 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add]
  have h1 : (fun t : ℝ => f t - f 0 - t • b) =O[𝓝 0] fun t : ℝ => t ^ 2 := by
    refine Asymptotics.IsBigO.of_bound K ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
    have := h t (by simpa using ht)
    rwa [norm_pow, Real.norm_eq_abs, sq, ← mul_assoc]
  exact h1.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

end GlobalTheory.TypeSum.FamClosed

open GlobalTheory.TypeSum.FamClosed in

theorem GlobalTheory.TypeSum.isClosed_fam (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ρ : Mx n → (E →L[ℂ] E)) (hρ : ModRep ε ρ) : IsClosed (Fam ε ρ : Set (List (lie (Jm ε)) → E)) := by
  obtain ⟨h1, hmul, C, N, hC⟩ := hρ
  refine isClosed_of_closure_subset fun v hv => ⟨fun l X => ?_, fun l₁ l₂ a X Y => ?_, fun l₁ l₂ X Y Z hZ => ?_⟩
  · have hX : (X : Mx n) ∈ lieSet ε := X.2
    have h0 : ρ (NormedSpace.exp ((0 : ℝ) • (X : Mx n))) = 1 := by rw [zero_smul, NormedSpace.exp_zero, h1]
    have hR : ∀ s t : ℝ, ρ (NormedSpace.exp ((s + t) • (X : Mx n))) =
        (ρ (NormedSpace.exp (s • (X : Mx n)))).comp (ρ (NormedSpace.exp (t • (X : Mx n)))) := fun s t => by
      rw [exp_add_smul, hmul _ (exp_mem_UJ hX s) _ (exp_mem_UJ hX t)]
    have hc : Continuous fun s : ℝ => C * (1 + hs (NormedSpace.exp (s • (X : Mx n)))) ^ N :=
      continuous_const.mul ((continuous_const.add (continuous_hs.comp (continuous_exp_smul _))).pow N)
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℝ) 1).bddAbove_image hc.continuousOn
    have hM' : ∀ s : ℝ, |s| ≤ 1 → ‖ρ (NormedSpace.exp (s • (X : Mx n)))‖ ≤ M := fun s hs =>
      (hC _ (exp_mem_UJ hX s)).trans (hM ⟨s, by simpa using hs, rfl⟩)
    refine hasDerivAt_of_bound (K := M * ‖v (X :: X :: l)‖) fun t ht => ?_
    simp only [h0, ContinuousLinearMap.one_apply]
    have hcl : IsClosed {w : List (lie (Jm ε)) → E |
        ‖ρ (NormedSpace.exp (t • (X : Mx n))) (w l) - w l - t • w (X :: l)‖ ≤ M * ‖w (X :: X :: l)‖ * |t| * |t|} :=
      isClosed_le (by fun_prop) (by fun_prop)
    exact closure_minimal (fun w hw => taylor_bound (R := fun s : ℝ => ρ (NormedSpace.exp (s • (X : Mx n))))
      h0 hR hM' (hw.1 l X) (hw.1 (X :: l) X) ht) hcl hv
  · have hcl : IsClosed {w : List (lie (Jm ε)) → E |
        w (l₁ ++ (a • X + Y) :: l₂) = (a : ℂ) • w (l₁ ++ X :: l₂) + w (l₁ ++ Y :: l₂)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact closure_minimal (fun w hw => hw.2.1 l₁ l₂ a X Y) hcl hv
  · have hcl : IsClosed {w : List (lie (Jm ε)) → E |
        w (l₁ ++ X :: Y :: l₂) - w (l₁ ++ Y :: X :: l₂) = w (l₁ ++ Z :: l₂)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact closure_minimal (fun w hw => hw.2.2 l₁ l₂ X Y Z hZ) hcl hv
