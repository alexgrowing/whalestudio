import Formalism.UnipotentAdelicQuotients.EllRegCut

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

variable {d : ℕ}

private theorem norm_eF_eq_one (ξ y : E d) : ‖eF ξ y‖ = 1 := by
  unfold eF
  have h : -(2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ y ξ : ℝ) : ℂ)) =
      ((-(2 * Real.pi * inner ℝ y ξ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem fourier_eq_integral_eF_mul (f : E d → ℂ) (ζ : E d) :
    𝓕 f ζ = ∫ x, eF ζ x * f x := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  try dsimp only
  rw [smul_eq_mul]
  unfold eF
  congr 1; congr 1; push_cast; ring

private theorem fourierInv_eq_integral_eF_neg_mul (F : E d → ℂ) (y : E d) :
    𝓕⁻ F y = ∫ η, eF (-η) y * F η := by
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  try dsimp only
  rw [smul_eq_mul]
  unfold eF
  rw [inner_neg_right, real_inner_comm]
  congr 1; congr 1; push_cast; ring

theorem pf_parseval (g k : E d → ℂ) (hg : Integrable g) (hkc : Continuous k)
    (hk : Integrable k) (hK : Integrable (𝓕 k)) :
    ∫ y, g y * k y = ∫ η, 𝓕 k (-η) * 𝓕 g η := by
  have hinv : ∀ y, k y = ∫ η, eF (-η) y * 𝓕 k η := by
    intro y
    rw [← fourierInv_eq_integral_eF_neg_mul]
    exact (congrFun (hkc.fourierInv_fourier_eq hk hK) y).symm
  have hcχ : Continuous fun p : E d × E d => eF (-p.2) p.1 := by
    unfold eF
    fun_prop
  have hint_r : Integrable (fun p : E d × E d => g p.1 * (eF (-p.2) p.1 * 𝓕 k p.2))
      (volume.prod volume) := by
    have hprod : Integrable (fun p : E d × E d => g p.1 * 𝓕 k p.2) (volume.prod volume) := by
      exact hg.mul_prod hK
    refine hprod.mono ?_ (Filter.Eventually.of_forall fun p => le_of_eq ?_)
    · first
      | exact hg.1.fst.mul (hcχ.aestronglyMeasurable.mul hK.1.snd)
      | exact hg.1.comp_fst.mul (hcχ.aestronglyMeasurable.mul hK.1.comp_snd)
    · try dsimp only
      rw [norm_mul, norm_mul, norm_mul, norm_eF_eq_one, one_mul]
  calc ∫ y, g y * k y = ∫ y, ∫ η, g y * (eF (-η) y * 𝓕 k η) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        try dsimp only
        rw [integral_const_mul, ← hinv y]
    _ = ∫ η, ∫ y, g y * (eF (-η) y * 𝓕 k η) := integral_integral_swap hint_r
    _ = ∫ η, 𝓕 k η * 𝓕 g (-η) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
        try dsimp only
        rw [fourier_eq_integral_eF_mul g (-η), ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        try dsimp only
        ring
    _ = ∫ η, 𝓕 k (-η) * 𝓕 g η := by
        exact ((integral_neg_eq_self (fun η => 𝓕 k η * 𝓕 g (-η)) volume).symm).trans (by simp only [neg_neg])

private theorem contDiff_infty_fderiv_of_contDiff_infty {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fderiv ℝ f) := by
  exact (contDiff_infty_iff_fderiv.1 hf).2

theorem pf_dw_smooth (L : List (Fin d)) (k : E d → ℂ) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) :
    ContDiff ℝ ∞ (dw L k) ∧ HasCompactSupport (dw L k) := by
  induction L with
  | nil => exact ⟨hk, hkc⟩
  | cons j w ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · show ContDiff ℝ ∞ (fun x => fderiv ℝ (dw w k) x (ev j))
      exact (contDiff_infty_fderiv_of_contDiff_infty h1).clm_apply contDiff_const
    · show HasCompactSupport (fun x => fderiv ℝ (dw w k) x (ev j))
      refine (h2.fderiv ℝ).mono ?_
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h0
      apply hx
      rw [h0]
      simp

private theorem differentiable_of_contDiff_infty {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f := by
  exact (contDiff_infty_iff_fderiv.1 hf).1

private theorem exists_clm_eq_neg_two_pi_I_inner (ζ : E d) :
    ∃ L : E d →L[ℝ] ℂ, ∀ x, L x = -(2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ x ζ : ℝ) : ℂ)) := by
  refine ⟨(-(2 * (Real.pi : ℂ) * Complex.I)) • (Complex.ofRealCLM.comp (innerSL ℝ ζ)), fun x => ?_⟩
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  rw [innerSL_apply_apply, real_inner_comm]; ring

private theorem eF_eq_exp_comp_of_clm (ζ : E d) (L : E d →L[ℝ] ℂ)
    (hL : ∀ x, L x = -(2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ x ζ : ℝ) : ℂ))) :
    eF ζ = fun x => Complex.exp (L x) := by
  funext x; rw [hL]; rfl

set_option maxHeartbeats 800000 in

theorem pf_fourier_fderiv (k : E d → ℂ) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) (v ζ : E d) :
    𝓕 (fun x => fderiv ℝ k x v) ζ = (2 * Real.pi * Complex.I * ((inner ℝ ζ v : ℝ) : ℂ)) * 𝓕 k ζ := by
  obtain ⟨L, hL⟩ := exists_clm_eq_neg_two_pi_I_inner ζ
  have hχ := eF_eq_exp_comp_of_clm ζ L hL
  have hχd : ∀ x, HasFDerivAt (eF ζ) (Complex.exp (L x) • L) x := by
    intro x; rw [hχ]; exact L.hasFDerivAt.cexp
  have hχfd : ∀ x, fderiv ℝ (eF ζ) x v = eF ζ x * L v := by
    intro x
    rw [(hχd x).fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul, hχ]
  have hχc : Continuous (eF ζ) := by rw [hχ]; exact Complex.continuous_exp.comp L.continuous
  have hkd : Differentiable ℝ k := differentiable_of_contDiff_infty hk
  have hχdiff : Differentiable ℝ (eF ζ) := fun x => (hχd x).differentiableAt
  have hDc : Continuous (fun x => fderiv ℝ k x v) := (contDiff_infty_fderiv_of_contDiff_infty hk).continuous.clm_apply continuous_const
  have hDs : HasCompactSupport (fun x => fderiv ℝ k x v) := by
    refine (hkc.fderiv ℝ).mono ?_
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    rw [h0]
    simp
  have i1 : Integrable (fun x => fderiv ℝ (eF ζ) x v * k x) := by
    have e : (fun x => fderiv ℝ (eF ζ) x v * k x) = fun x => eF ζ x * L v * k x := by
      funext x; rw [hχfd]
    rw [e]
    exact ((hχc.mul continuous_const).mul hk.continuous).integrable_of_hasCompactSupport hkc.mul_left
  have i2 : Integrable (fun x => eF ζ x * fderiv ℝ k x v) :=
    (hχc.mul hDc).integrable_of_hasCompactSupport hDs.mul_left
  have i3 : Integrable (fun x => eF ζ x * k x) :=
    (hχc.mul hk.continuous).integrable_of_hasCompactSupport hkc.mul_left
  have hibp : ∫ x, eF ζ x * fderiv ℝ k x v = -∫ x, fderiv ℝ (eF ζ) x v * k x := by
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3 (fun x _ => hχdiff x) (fun x _ => hkd x)
  rw [fourier_eq_integral_eF_mul, fourier_eq_integral_eF_mul, hibp]
  have e2 : (fun x => fderiv ℝ (eF ζ) x v * k x) = fun x => L v * (eF ζ x * k x) := by
    funext x; rw [hχfd]; ring
  rw [e2, integral_const_mul, hL v, real_inner_comm]
  ring

theorem pf_fourier_dw (L : List (Fin d)) (k : E d → ℂ) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (ζ : E d) :
    𝓕 (dw L k) ζ = (L.map fun j => 2 * Real.pi * Complex.I * ((ζ j : ℝ) : ℂ)).prod * 𝓕 k ζ := by
  induction L with
  | nil => simp [dw]
  | cons j w ih =>
    obtain ⟨h1, h2⟩ := pf_dw_smooth w k hk hkc
    show 𝓕 (fun x => fderiv ℝ (dw w k) x (ev j)) ζ = _
    rw [pf_fourier_fderiv _ h1 h2, ih, List.map_cons, List.prod_cons]
    have hb : inner ℝ ζ (ev j) = ζ j := by
      simp [ev, EuclideanSpace.inner_single_right]
    rw [hb]; ring

theorem pf_modulate (b : E d → ℂ) (ξ ζ : E d) : 𝓕 (fun y => b y * eF ξ y) ζ = 𝓕 b (ζ + ξ) := by
  rw [fourier_eq_integral_eF_mul, fourier_eq_integral_eF_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  try dsimp only
  have h : eF ζ y * eF ξ y = eF (ζ + ξ) y := by
    simp only [eF, ← Complex.exp_add, inner_add_right]
    congr 1; push_cast; ring
  rw [← h]; ring

theorem pf_fourier_integrable (k : E d → ℂ) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) :
    Integrable (𝓕 k) := by
  have hdecay : ∀ m n : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ m * ‖iteratedFDeriv ℝ n k x‖ ≤ C := by
    intro m n
    have hcn : Continuous fun x => iteratedFDeriv ℝ n k x := by
      exact hk.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    have hc : Continuous fun x : E d => ‖x‖ ^ m * ‖iteratedFDeriv ℝ n k x‖ :=
      (continuous_norm.pow m).mul hcn.norm
    have hs : HasCompactSupport fun x : E d => ‖x‖ ^ m * ‖iteratedFDeriv ℝ n k x‖ :=
      ((hkc.iteratedFDeriv (𝕜 := ℝ) n).norm).mul_left
    obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
    exact ⟨C, fun x => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC x)⟩
  let S : SchwartzMap (E d) ℂ := ⟨k, hk, hdecay⟩
  exact (SchwartzMap.fourierTransformCLM ℂ S).integrable

theorem pf_eF_smooth (ξ : E d) : ContDiff ℝ ∞ (eF ξ) := by
  obtain ⟨L, hL⟩ := exists_clm_eq_neg_two_pi_I_inner ξ
  rw [eF_eq_exp_comp_of_clm ξ L hL]
  exact Complex.contDiff_exp.comp L.contDiff

theorem pf_sign (n : ℕ) (w : Fin n → Fin d) (η : E d) :
    (-1 : ℂ) ^ n * ∏ l, (2 * Real.pi * Complex.I * (((-η) (w l) : ℝ) : ℂ)) = mono w η := by
  unfold mono
  have h : ∀ l, (2 * (Real.pi : ℂ) * Complex.I * (((-η) (w l) : ℝ) : ℂ)) =
      (-1) * (2 * Real.pi * Complex.I * ((η (w l) : ℝ) : ℂ)) := by
    intro l
    rw [PiLp.neg_apply]; push_cast; ring
  rw [Finset.prod_congr rfl (fun l _ => h l), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← mul_assoc, ← mul_pow]
  norm_num

theorem adjointPairingFourier : PairingFourier := by
  intro d m b g hb hg hgc ξ
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have term : ∀ n (w : Fin n → Fin d),
      ∫ y, g y * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * eF ξ y) y) =
        conv (𝓕 (b n w)) (fun η => mono w η * 𝓕 g η) ξ := by
    intro n w
    have hs : ContDiff ℝ ∞ (fun y => b n w y * eF ξ y) := (hb n w).1.mul (pf_eF_smooth ξ)
    have hc : HasCompactSupport (fun y => b n w y * eF ξ y) := (hb n w).2.mul_right
    obtain ⟨D1, D2⟩ := pf_dw_smooth (List.ofFn w) _ hs hc
    have hD := pf_parseval g _ hgi D1.continuous (D1.continuous.integrable_of_hasCompactSupport D2)
      (pf_fourier_integrable _ D1 D2)
    calc ∫ y, g y * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * eF ξ y) y)
        = (-1 : ℂ) ^ n * ∫ y, g y * dw (List.ofFn w) (fun y => b n w y * eF ξ y) y := by
          rw [← integral_const_mul]
          congr 1
          ext y
          ring
      _ = ∫ η, (-1 : ℂ) ^ n * (𝓕 (dw (List.ofFn w) (fun y => b n w y * eF ξ y)) (-η) * 𝓕 g η) := by
          rw [hD, integral_const_mul]
      _ = conv (𝓕 (b n w)) (fun η => mono w η * 𝓕 g η) ξ := by
          unfold conv
          congr 1
          ext η
          rw [pf_fourier_dw _ _ hs hc, pf_modulate, List.map_ofFn, List.prod_ofFn, neg_add_eq_sub]
          simp only [Function.comp_apply]
          rw [← pf_sign n w η]
          ring
  have hint : ∀ n (w : Fin n → Fin d),
      Integrable (fun y => g y * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * eF ξ y) y)) := by
    intro n w
    obtain ⟨D1, D2⟩ := pf_dw_smooth (List.ofFn w) _ ((hb n w).1.mul (pf_eF_smooth ξ)) (hb n w).2.mul_right
    exact (hg.mul (continuous_const.mul D1.continuous)).integrable_of_hasCompactSupport hgc.mul_right
  calc ∫ y, g y * trOp m b (eF ξ) y
      = ∫ y, ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
          g y * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * eF ξ y) y) := by
        congr 1
        ext y
        simp only [trOp, Finset.mul_sum]
    _ = ∑ n ∈ Finset.range (m + 1), ∫ y, ∑ w : Fin n → Fin d,
          g y * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * eF ξ y) y) :=
        integral_finsetSum _ (fun n _ => integrable_finsetSum _ (fun w _ => hint n w))
    _ = ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
          ∫ y, g y * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * eF ξ y) y) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        exact integral_finsetSum _ (fun w _ => hint n w)
    _ = ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d, conv (𝓕 (b n w)) (fun η => mono w η * 𝓕 g η) ξ := by
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
        exact term n w

end

end ZetaZeros.D.EllReg
