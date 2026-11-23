import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobSym

namespace Formalism.IndefR.Eqv

open scoped ContDiff
open Filter Topology

section MD

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def md (φ : V → ℂ) : (n : ℕ) → (Fin n → V) → ℝ → V → ℂ
  | 0, _, _, a => φ a
  | n + 1, v, h, a => (md φ n (Fin.tail v) h (a + h • v 0) - md φ n (Fin.tail v) h a) / h

theorem hasDerivAt_md_along_line {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ) : ∀ (n : ℕ) (v : Fin n → V) (h : ℝ) (a w : V),
    HasDerivAt (fun s : ℝ => md φ n v h (a + s • w)) (md (fun y => fderiv ℝ φ y w) n v h a) 0
  | 0, v, h, a, w => by
    simp only [md]
    have h1 : HasDerivAt (fun s : ℝ => a + s • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add a
    exact ((hφ.differentiable (by simp)) a).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
  | n + 1, v, h, a, w => by
    simp only [md]
    have e1 : ∀ s : ℝ, a + s • w + h • v 0 = (a + h • v 0) + s • w := fun s => by abel
    have h1 := hasDerivAt_md_along_line hφ n (Fin.tail v) h (a + h • v 0) w
    have h2 := hasDerivAt_md_along_line hφ n (Fin.tail v) h a w
    simp_rw [e1]
    exact (h1.sub h2).div_const h

end MD

section MD2

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem snoc_eq_cons_rot {n : ℕ} (w : V) (vs : Fin n → V) :
    (Fin.snoc vs w : Fin (n + 1) → V) = (Fin.cons w vs : Fin (n + 1) → V) ∘ finRotate (n + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [finRotate_last]
  · simp only [Fin.snoc_castSucc, Function.comp_apply]
    rw [finRotate_succ_apply, Fin.coeSucc_eq_succ, Fin.cons_succ]

theorem iter_fderiv_apply {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (w : V) (a : V) (vs : Fin n → V) :
    iteratedFDeriv ℝ n (fun y => fderiv ℝ φ y w) a vs = iteratedFDeriv ℝ (n + 1) φ a (Fin.cons w vs) := by
  have hf : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (m := ∞) (by simp)
  have e1 : (fun y => fderiv ℝ φ y w) = (ContinuousLinearMap.apply ℝ ℂ w) ∘ fderiv ℝ φ := rfl
  rw [e1, ContinuousLinearMap.iteratedFDeriv_comp_left _ hf.contDiffAt (natCast_lt_inf' n).le]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply]
  have e2 : iteratedFDeriv ℝ (n + 1) φ a (Fin.snoc vs w) = iteratedFDeriv ℝ n (fderiv ℝ φ) a vs w := by
    rw [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  rw [← e2, snoc_eq_cons_rot, iterSymmR V ℂ φ hφ (n + 1) a _ (finRotate (n + 1))]

theorem contDiff_fderiv_apply {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ) (w : V) : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y w) :=
  (ContinuousLinearMap.apply ℝ ℂ w).contDiff.comp (hφ.fderiv_right (m := ∞) (by simp))

theorem md_succ_sub (φ : V → ℂ) (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (v : Fin (n + 1) → V) {h : ℝ} (hh : 0 < h) (b : V)
    (T : ℂ) (ε : ℝ) (hε : ∀ s ∈ Set.Icc (0 : ℝ) h,
      ‖md (fun y => fderiv ℝ φ y (v 0)) n (Fin.tail v) h (b + s • v 0) - T‖ ≤ ε) :
    ‖md φ (n + 1) v h b - T‖ ≤ ε := by
  set F : ℝ → ℂ := fun s => md φ n (Fin.tail v) h (b + s • v 0) - s • T
  have hF : ∀ s, HasDerivAt F (md (fun y => fderiv ℝ φ y (v 0)) n (Fin.tail v) h (b + s • v 0) - T) s := by
    intro s
    have h1 := hasDerivAt_md_along_line hφ n (Fin.tail v) h (b + s • v 0) (v 0)
    have h1' : HasDerivAt (fun r : ℝ => md φ n (Fin.tail v) h (b + s • v 0 + r • v 0))
        (md (fun y => fderiv ℝ φ y (v 0)) n (Fin.tail v) h (b + s • v 0)) (s - s) := by
      rw [sub_self]; exact h1
    have h2 := HasDerivAt.comp_sub_const s s h1'
    have h3 : HasDerivAt (fun r : ℝ => md φ n (Fin.tail v) h (b + r • v 0))
        (md (fun y => fderiv ℝ φ y (v 0)) n (Fin.tail v) h (b + s • v 0)) s := by
      refine h2.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
      show md φ n (Fin.tail v) h (b + r • v 0) = md φ n (Fin.tail v) h (b + s • v 0 + (r - s) • v 0)
      rw [add_assoc, ← add_smul, add_sub_cancel]
    have h4 := h3.sub ((hasDerivAt_id s).smul_const T)
    rw [one_smul] at h4
    exact h4
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := F) (a := 0) (b := h) (C := ε)
    (fun s _ => (hF s).hasDerivWithinAt) (fun s hs => hε s ⟨hs.1, hs.2.le⟩)
  have hb := hmv h ⟨hh.le, le_rfl⟩
  have hFe : F h - F 0 = md φ n (Fin.tail v) h (b + h • v 0) - h • T - md φ n (Fin.tail v) h b := by
    simp only [F, zero_smul, add_zero, sub_zero]
  rw [hFe, sub_zero] at hb
  have e : md φ (n + 1) v h b - T =
      ((h : ℂ))⁻¹ * (md φ n (Fin.tail v) h (b + h • v 0) - h • T - md φ n (Fin.tail v) h b) := by
    simp only [md]
    rw [Complex.real_smul]
    have : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    field_simp
    ring
  rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hh.le]
  calc h⁻¹ * ‖md φ n (Fin.tail v) h (b + h • v 0) - h • T - md φ n (Fin.tail v) h b‖
      ≤ h⁻¹ * (ε * h) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh.le)
    _ = ε := by field_simp

end MD2

section MD3

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem md_tendsto : ∀ (n : ℕ) (φ : V → ℂ), ContDiff ℝ ∞ φ → ∀ (v : Fin n → V) (a : V) (ε : ℝ), 0 < ε →
    ∃ δ > 0, ∀ h, 0 < h → h < δ → ∀ b, ‖b - a‖ < δ → ‖md φ n v h b - iteratedFDeriv ℝ n φ a v‖ ≤ ε
  | 0, φ, hφ, v, a, ε, hε => by
    obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.mp hφ.continuous a ε hε
    refine ⟨δ, hδ, fun h _ _ b hb => ?_⟩
    simp only [md, iteratedFDeriv_zero_apply]
    have := hδε b (by rw [dist_eq_norm]; exact hb)
    rw [dist_eq_norm] at this
    exact this.le
  | n + 1, φ, hφ, v, a, ε, hε => by
    obtain ⟨δ1, hδ1, hIH⟩ := md_tendsto n (fun y => fderiv ℝ φ y (v 0)) (contDiff_fderiv_apply hφ (v 0))
      (Fin.tail v) a ε hε
    have hw : 0 < ‖v 0‖ + 1 := by positivity
    refine ⟨δ1 / (2 * (‖v 0‖ + 1)), by positivity, fun h hh hhδ b hb => ?_⟩
    have hT : iteratedFDeriv ℝ (n + 1) φ a v =
        iteratedFDeriv ℝ n (fun y => fderiv ℝ φ y (v 0)) a (Fin.tail v) := by
      rw [iter_fderiv_apply hφ, Fin.cons_self_tail]
    rw [hT]
    refine md_succ_sub φ hφ n v hh b _ ε fun s hs => hIH h hh ?_ _ ?_
    · have : δ1 / (2 * (‖v 0‖ + 1)) ≤ δ1 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [norm_nonneg (v 0)]
      linarith
    · calc ‖b + s • v 0 - a‖ = ‖(b - a) + s • v 0‖ := by congr 1; abel
        _ ≤ ‖b - a‖ + s * ‖v 0‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_of_nonneg hs.1]
        _ < δ1 := by
          have h1 : s * ‖v 0‖ ≤ h * ‖v 0‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
          have h2 : h * ‖v 0‖ ≤ δ1 / (2 * (‖v 0‖ + 1)) * (‖v 0‖ + 1) :=
            mul_le_mul hhδ.le (by linarith) (norm_nonneg _) (by positivity)
          have h3 : δ1 / (2 * (‖v 0‖ + 1)) * (‖v 0‖ + 1) = δ1 / 2 := by field_simp
          have h4 : δ1 / (2 * (‖v 0‖ + 1)) ≤ δ1 / 2 := by
            apply div_le_div_of_nonneg_left hδ1.le (by norm_num); nlinarith [norm_nonneg (v 0)]
          linarith

theorem norm_iter_fderiv_apply_le {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (w y : V) :
    ‖iteratedFDeriv ℝ n (fun z => fderiv ℝ φ z w) y‖ ≤ ‖iteratedFDeriv ℝ (n + 1) φ y‖ * ‖w‖ := by
  have hf : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (m := ∞) (by simp)
  have e1 : (fun z => fderiv ℝ φ z w) = (ContinuousLinearMap.apply ℝ ℂ w) ∘ fderiv ℝ φ := rfl
  rw [e1]
  refine ((ContinuousLinearMap.apply ℝ ℂ w).norm_iteratedFDeriv_comp_left hf.contDiffAt
    (natCast_lt_inf' n).le).trans ?_
  have hA : ‖ContinuousLinearMap.apply ℝ ℂ w‖ ≤ ‖w‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun T => ?_
    rw [ContinuousLinearMap.apply_apply, mul_comm]
    exact T.le_opNorm w
  rw [norm_iteratedFDeriv_fderiv]
  calc _ ≤ ‖w‖ * ‖iteratedFDeriv ℝ (n + 1) φ y‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem md_bound : ∀ (n : ℕ) (φ : V → ℂ), ContDiff ℝ ∞ φ → ∀ (v : Fin n → V) (h : ℝ), 0 < h → ∀ (b : V) (M : ℝ),
    (∀ y, ‖y - b‖ ≤ h * ∑ i, ‖v i‖ → ‖iteratedFDeriv ℝ n φ y‖ ≤ M) → ‖md φ n v h b‖ ≤ M * ∏ i, ‖v i‖
  | 0, φ, hφ, v, h, hh, b, M, hM => by
    simp only [md, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    have := hM b (by simp)
    rwa [norm_iteratedFDeriv_zero] at this
  | n + 1, φ, hφ, v, h, hh, b, M, hM => by
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM b (by simp; positivity))
    have key := md_succ_sub φ hφ n v hh b 0 (M * ‖v 0‖ * ∏ i, ‖Fin.tail v i‖) fun s hs => by
      rw [sub_zero]
      refine md_bound n (fun y => fderiv ℝ φ y (v 0)) (contDiff_fderiv_apply hφ (v 0)) (Fin.tail v) h hh
        (b + s • v 0) (M * ‖v 0‖) fun y hy => ?_
      refine (norm_iter_fderiv_apply_le hφ n (v 0) y).trans (mul_le_mul_of_nonneg_right (hM y ?_) (norm_nonneg _))
      calc ‖y - b‖ = ‖(y - (b + s • v 0)) + s • v 0‖ := by congr 1; abel
        _ ≤ ‖y - (b + s • v 0)‖ + s * ‖v 0‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_smul, Real.norm_of_nonneg hs.1]
        _ ≤ h * ∑ i, ‖Fin.tail v i‖ + h * ‖v 0‖ := add_le_add hy (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _))
        _ = h * ∑ i, ‖v i‖ := by
          rw [Fin.sum_univ_succ]
          show h * ∑ i : Fin n, ‖v i.succ‖ + h * ‖v 0‖ = h * (‖v 0‖ + ∑ i : Fin n, ‖v i.succ‖)
          ring
    rw [sub_zero] at key
    refine key.trans (le_of_eq ?_)
    rw [Fin.prod_univ_succ]
    show M * ‖v 0‖ * ∏ i : Fin n, ‖v i.succ‖ = M * (‖v 0‖ * ∏ i : Fin n, ‖v i.succ‖)
    ring

end MD3

end Formalism.IndefR.Eqv
