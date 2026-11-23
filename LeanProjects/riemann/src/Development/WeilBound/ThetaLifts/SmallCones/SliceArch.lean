import Mathlib

noncomputable section

namespace PositivityTheory.ThKCT.Arch

open scoped ContDiff NNReal
open Complex Filter Topology

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def Bd (m : ℕ) (f : V → ℂ) (C : ℝ) : Prop := ∀ j ≤ m, ∀ x, (1 + ‖x‖) ^ m * ‖iteratedFDeriv ℝ j f x‖ ≤ C

variable (V) in

def P (m : ℕ) : Seminorm ℂ (SchwartzMap V ℂ) := (Finset.Iic (m, m)).sup (schwartzSeminormFamily ℂ V ℂ)

theorem P_cont (m : ℕ) : Continuous (P V m) :=
  Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i

def sc {Z : Type} [AddCommGroup Z] [Module ℂ Z] (C : ℝ) (p : Seminorm ℂ Z) : Seminorm ℂ Z := C.toNNReal • p

theorem sc_apply {Z : Type} [AddCommGroup Z] [Module ℂ Z] {C : ℝ} (h : 0 ≤ C) (p : Seminorm ℂ Z) (f : Z) : sc C p f = C * p f := by
  rw [sc, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ h]

theorem sc_cont {Z : Type} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] (C : ℝ) {p : Seminorm ℂ Z} (h : Continuous p) :
    Continuous (sc C p) := ((continuous_const (y := (C.toNNReal : ℝ))).mul h).congr fun f => by
  rw [sc, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]; rfl

theorem bd_P (m : ℕ) (f : SchwartzMap V ℂ) : Bd m f (2 ^ m * P V m f) := fun j hj x =>
  SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (m, m)) le_rfl hj f x

theorem Bd.nonneg {m : ℕ} {f : V → ℂ} {C : ℝ} (h : Bd m f C) : 0 ≤ C :=
  le_trans (by positivity) (h 0 (Nat.zero_le _) 0)

theorem Bd.mono {m : ℕ} {f : V → ℂ} {C C' : ℝ} (h : Bd m f C) (hC : C ≤ C') : Bd m f C' :=
  fun j hj x => (h j hj x).trans hC

theorem Bd.succ {m : ℕ} {f : V → ℂ} {C : ℝ} (h : Bd (m + 1) f C) : Bd m f C := fun j hj x =>
  le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [norm_nonneg x]) (Nat.le_succ m)) (norm_nonneg _))
    (h j (hj.trans (Nat.le_succ m)) x)

theorem P_le {m : ℕ} {f : SchwartzMap V ℂ} {C : ℝ} (h : Bd m f C) : P V m f ≤ C := by
  refine Seminorm.finset_sup_apply_le h.nonneg fun i hi => ?_
  have hi' := Finset.mem_Iic.1 hi
  refine SchwartzMap.seminorm_le_bound ℂ i.1 i.2 f h.nonneg fun x => le_trans ?_ (h i.2 hi'.2 x)
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact (pow_le_pow_left₀ (norm_nonneg x) (by linarith) _).trans
    (pow_le_pow_right₀ (by linarith [norm_nonneg x]) hi'.1)

theorem exists_P (q : Seminorm ℂ (SchwartzMap V ℂ)) (hq : Continuous q) : ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ f, q f ≤ C * P V m f := by
  obtain ⟨s, C, -, h⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) q hq
  refine ⟨s.sup fun i => max i.1 i.2, C, C.2, fun f => (h f).trans ?_⟩
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left (Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi => ?_) C.2
  have := Finset.le_sup (f := fun i : ℕ × ℕ => max i.1 i.2) hi
  exact Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 ⟨(le_max_left _ _).trans this, (le_max_right _ _).trans this⟩)

theorem peetre (x y : V) {r : ℝ} (h : ‖y - x‖ ≤ r) : 1 + ‖x‖ ≤ (1 + r) * (1 + ‖y‖) := by
  have h1 : ‖x‖ ≤ ‖y‖ + ‖y - x‖ := by simpa using norm_sub_le y (y - x)
  nlinarith [norm_nonneg y, norm_nonneg (y - x)]

theorem Bd.shift {m : ℕ} {f : V → ℂ} {C : ℝ} (h : Bd m f C) (t : V) : Bd m (fun x => f (x + t)) ((1 + ‖t‖) ^ m * C) := by
  intro j hj x
  rw [iteratedFDeriv_comp_add_right]
  refine le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
    (peetre x (x + t) (r := ‖t‖) (by simp)) m) (norm_nonneg _)) ?_
  rw [mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h j hj _) (by positivity)

theorem Bd.shift_sub {m : ℕ} {f : V → ℂ} (hf : ContDiff ℝ ∞ f) {C : ℝ} (h : Bd (m + 1) f C) (t : V) :
    Bd m (fun x => f (x + t) - f x) ((1 + ‖t‖) ^ m * C * ‖t‖) := by
  intro j hj x
  have hj' : ContDiff ℝ j f := hf.of_le (by exact_mod_cast le_top)
  have e : iteratedFDeriv ℝ j (fun x => f (x + t) - f x) x = iteratedFDeriv ℝ j f (x + t) - iteratedFDeriv ℝ j f x := by
    rw [← iteratedFDeriv_comp_add_right]
    exact iteratedFDeriv_sub_apply (f := fun x => f (x + t)) (hj'.comp (contDiff_id.add contDiff_const)).contDiffAt hj'.contDiffAt
  have hd : Differentiable ℝ (iteratedFDeriv ℝ j f) := hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top j)
  have hp : 0 < (1 + ‖x‖) ^ m := by positivity
  have := (convex_closedBall x ‖t‖).norm_image_sub_le_of_norm_fderiv_le (f := iteratedFDeriv ℝ j f)
    (C := (1 + ‖t‖) ^ m * C / (1 + ‖x‖) ^ m) (fun y _ => hd y) (fun y hy => by
      rw [norm_fderiv_iteratedFDeriv, le_div_iff₀ hp, mul_comm]
      refine le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
        (peetre x y (r := ‖t‖) (by simpa [dist_eq_norm] using hy)) m) (norm_nonneg _)) ?_
      rw [mul_pow, mul_assoc]
      refine mul_le_mul_of_nonneg_left (le_trans ?_ (h (j + 1) (by omega) y)) (by positivity)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [norm_nonneg y]) (Nat.le_succ m)) (norm_nonneg _))
    (Metric.mem_closedBall_self (norm_nonneg t)) (y := x + t) (by simp)
  rw [e, mul_comm, ← le_div_iff₀ hp]
  refine this.trans (le_of_eq ?_)
  rw [add_sub_cancel_left]; ring

theorem Bd.mul {m r : ℕ} {a f : V → ℂ} (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) {A C : ℝ}
    (hA : ∀ i ≤ m, ∀ x, ‖iteratedFDeriv ℝ i a x‖ ≤ A * (1 + ‖x‖) ^ r) (h : Bd (m + r) f C) :
    Bd m (fun x => a x * f x) (2 ^ m * (A * C)) := by
  intro j hj x
  have hA0 : 0 ≤ A := by
    have := (norm_nonneg _).trans (hA 0 (Nat.zero_le _) 0)
    simpa using this
  have h1 := norm_iteratedFDeriv_mul_le ha hf x (n := j) (by exact_mod_cast le_top)
  refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ?_
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum (g := fun i => (j.choose i : ℝ) * (A * C)) fun i hi => ?_).trans ?_
  · have hi' := Finset.mem_range.1 hi
    have h2 := h (j - i) (by omega) x
    have h3 := hA i (by omega) x
    calc _ = (j.choose i : ℝ) * (‖iteratedFDeriv ℝ i a x‖ * ((1 + ‖x‖) ^ m * ‖iteratedFDeriv ℝ (j - i) f x‖)) := by ring
      _ ≤ (j.choose i : ℝ) * ((A * (1 + ‖x‖) ^ r) * ((1 + ‖x‖) ^ m * ‖iteratedFDeriv ℝ (j - i) f x‖)) := by gcongr
      _ = (j.choose i : ℝ) * (A * ((1 + ‖x‖) ^ (m + r) * ‖iteratedFDeriv ℝ (j - i) f x‖)) := by ring
      _ ≤ _ := by gcongr
  · rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hA0 h.nonneg)
    push_cast
    exact pow_le_pow_right₀ one_le_two hj

theorem Bd.add {m : ℕ} {f g : V → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {C D : ℝ} (h : Bd m f C) (h' : Bd m g D) :
    Bd m (fun x => f x + g x) (C + D) := by
  intro j hj x
  rw [show iteratedFDeriv ℝ j (fun x => f x + g x) x = _ from iteratedFDeriv_add_apply
    (hf.of_le (by exact_mod_cast le_top)).contDiffAt (hg.of_le (by exact_mod_cast le_top)).contDiffAt]
  refine le_trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)) ?_
  rw [mul_add]
  exact add_le_add (h j hj x) (h' j hj x)

def ph (l : V →L[ℝ] ℝ) (c : ℝ) (x : V) : ℂ := cexp (I * ((l x + c : ℝ) : ℂ))

theorem u_smooth (c : ℝ) : ContDiff ℝ ∞ fun s : ℝ => cexp (I * ((s + c : ℝ) : ℂ)) :=
  (contDiff_const.mul (ofRealCLM.contDiff.comp (contDiff_id.add contDiff_const))).cexp

theorem ph_smooth (l : V →L[ℝ] ℝ) (c : ℝ) : ContDiff ℝ ∞ (ph l c) := (u_smooth c).comp l.contDiff

theorem u_deriv (c : ℝ) (i : ℕ) :
    iteratedDeriv i (fun s : ℝ => cexp (I * ((s + c : ℝ) : ℂ))) = fun s : ℝ => I ^ i * cexp (I * ((s + c : ℝ) : ℂ)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    have h : HasDerivAt (fun s : ℝ => ((s + c : ℝ) : ℂ)) 1 s := ((hasDerivAt_id s).add_const c).ofReal_comp
    rw [(((h.const_mul I).cexp).const_mul (I ^ i)).deriv]
    ring

theorem ph_bd (l : V →L[ℝ] ℝ) (c : ℝ) (i : ℕ) (x : V) : ‖iteratedFDeriv ℝ i (ph l c) x‖ ≤ ‖l‖ ^ i := by
  have e := l.iteratedFDeriv_comp_right (u_smooth c) x (i := i) (by exact_mod_cast le_top)
  rw [show ph l c = (fun s : ℝ => cexp (I * ((s + c : ℝ) : ℂ))) ∘ l from rfl, e]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans (le_of_eq ?_)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, u_deriv, norm_mul, norm_pow, norm_I, one_pow, mul_comm I, norm_exp_ofReal_mul_I]
  simp

theorem ph_temp (l : V →L[ℝ] ℝ) (c : ℝ) : (ph l c).HasTemperateGrowth :=
  ⟨ph_smooth l c, fun n => ⟨0, ‖l‖ ^ n, fun x => by simpa using ph_bd l c n x⟩⟩

theorem ph_sub_bd (l : V →L[ℝ] ℝ) (c : ℝ) {δ : ℝ} (h1 : δ ≤ 1) (hl : ‖l‖ ≤ δ) (hc : |c| ≤ δ) (i : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ i (fun x => ph l c x - 1) x‖ ≤ δ * (1 + ‖x‖) ^ 1 := by
  have h0 : 0 ≤ δ := (norm_nonneg _).trans hl
  rcases i with _ | i
  · rw [norm_iteratedFDeriv_zero, ph]
    refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ((norm_add_le _ _).trans ?_)
    have := l.le_opNorm x
    rw [Real.norm_eq_abs c]
    nlinarith [norm_nonneg x]
  · rw [show iteratedFDeriv ℝ (i + 1) (fun x => ph l c x - 1) x = _ from iteratedFDeriv_sub_apply
      ((ph_smooth l c).of_le (by exact_mod_cast le_top)).contDiffAt contDiffAt_const, iteratedFDeriv_succ_const]
    refine le_trans (by simpa using ph_bd l c (i + 1) x) ?_
    have : ‖l‖ ^ (i + 1) ≤ δ := (pow_le_of_le_one (norm_nonneg _) (hl.trans h1) (Nat.succ_ne_zero i)).trans hl
    nlinarith [norm_nonneg x]

def S (w : V × (V →L[ℝ] ℝ)) : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ :=
  (SchwartzMap.smulLeftCLM ℂ (ph w.2 (w.2 w.1 / 2))).comp (SchwartzMap.compSubConstCLM ℂ (-w.1))

theorem S_apply (w : V × (V →L[ℝ] ℝ)) (f : SchwartzMap V ℂ) (x : V) : S w f x = ph w.2 (w.2 w.1 / 2) x * f (x + w.1) := by
  rw [S, ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply (ph_temp _ _), SchwartzMap.compSubConstCLM_apply,
    sub_neg_eq_add, smul_eq_mul]

theorem shift_smooth (f : SchwartzMap V ℂ) (t : V) : ContDiff ℝ ∞ fun x => f (x + t) :=
  (f.smooth ⊤).comp (contDiff_id.add contDiff_const)

theorem grow (q : Seminorm ℂ (SchwartzMap V ℂ)) (hq : Continuous q) : ∃ (p : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ),
    Continuous p ∧ ∀ w f, q (S w f) ≤ (1 + ‖w‖) ^ M * p f := by
  obtain ⟨m, C, hC, h⟩ := exists_P q hq
  refine ⟨sc (C * 2 ^ m * 2 ^ m) (P V m), m + m, sc_cont _ (P_cont m), fun w f => (h _).trans ?_⟩
  have h1 := Bd.mul (r := 0) (A := (1 + ‖w‖) ^ m) (ph_smooth w.2 (w.2 w.1 / 2)) (shift_smooth f w.1) (fun i hi x => by
    refine (ph_bd _ _ _ _).trans ?_
    rw [pow_zero, mul_one]
    exact (pow_le_pow_left₀ (norm_nonneg _) ((norm_snd_le w).trans (by linarith)) _).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg w]) hi)) ((bd_P m f).shift w.1)
  have h2 := P_le (f := S w f) (by rw [show (S w f : V → ℂ) = _ from funext (S_apply w f)]; exact h1)
  rw [sc_apply (by positivity)]
  have h3 := norm_fst_le w
  have h4 := apply_nonneg (P V m) f
  calc _ ≤ C * (2 ^ m * ((1 + ‖w‖) ^ m * ((1 + ‖w‖) ^ m * (2 ^ m * P V m f)))) := by
        refine mul_le_mul_of_nonneg_left (h2.trans ?_) hC
        gcongr
    _ = _ := by ring

theorem lip (q : Seminorm ℂ (SchwartzMap V ℂ)) (hq : Continuous q) : ∃ p : Seminorm ℂ (SchwartzMap V ℂ),
    Continuous p ∧ ∀ w f, ‖w‖ ≤ 1 → q (S w f - f) ≤ ‖w‖ * p f := by
  obtain ⟨m, C, hC, h⟩ := exists_P q hq
  refine ⟨sc (C * (2 ^ m * 2 ^ (m + 1) * 2 ^ (m + 1) + 2 ^ m * 2 ^ (m + 1))) (P V (m + 1)),
    sc_cont _ (P_cont _), fun w f hw => (h _).trans ?_⟩
  have h3 := norm_fst_le w
  have hc : |w.2 w.1 / 2| ≤ ‖w‖ := by
    have := w.2.le_opNorm w.1
    rw [abs_div, abs_two, ← Real.norm_eq_abs]
    nlinarith [norm_snd_le w, norm_nonneg w.1, norm_nonneg w.2]
  have h1 := Bd.mul (m := m) ((ph_smooth w.2 (w.2 w.1 / 2)).sub contDiff_const) (shift_smooth f w.1)
    (fun i _ x => ph_sub_bd w.2 _ hw (norm_snd_le w) hc i x) ((bd_P (m + 1) f).shift w.1)
  have h2 := h1.add (((ph_smooth w.2 (w.2 w.1 / 2)).sub contDiff_const).mul (shift_smooth f w.1))
    ((shift_smooth f w.1).sub (f.smooth ⊤)) ((bd_P (m + 1) f).shift_sub (f.smooth ⊤) w.1)
  have h5 := P_le (f := S w f - f) (by
    rw [show ((S w f - f : SchwartzMap V ℂ) : V → ℂ) = _ from funext fun x => show _ =
      (ph w.2 (w.2 w.1 / 2) x - 1) * f (x + w.1) + (f (x + w.1) - f x) by rw [SchwartzMap.sub_apply, S_apply]; ring]
    exact h2)
  rw [sc_apply (by positivity)]
  have h4 := apply_nonneg (P V (m + 1)) f
  have h6 : 1 + ‖w.1‖ ≤ 2 := by linarith
  calc _ ≤ C * (2 ^ m * (‖w‖ * (2 ^ (m + 1) * (2 ^ (m + 1) * P V (m + 1) f))) + 2 ^ m * (2 ^ (m + 1) * P V (m + 1) f) * ‖w‖) := by
        refine mul_le_mul_of_nonneg_left (h5.trans ?_) hC
        gcongr
    _ = _ := by ring

theorem S_zero (f : SchwartzMap V ℂ) : S 0 f = f := by
  ext x
  simp [S_apply, ph]

theorem S_add (w h : V × (V →L[ℝ] ℝ)) (f : SchwartzMap V ℂ) :
    S (w + h) f = cexp (I * ((w.2 h.1 - h.2 w.1) / 2 : ℝ)) • S w (S h f) := by
  ext x
  rw [SchwartzMap.smul_apply, S_apply, S_apply, S_apply, ph, ph, ph, smul_eq_mul, ← mul_assoc, ← mul_assoc, ← Complex.exp_add,
    ← Complex.exp_add, Prod.fst_add, add_assoc x]
  congr 2
  simp only [Prod.snd_add, ContinuousLinearMap.add_apply, map_add]
  push_cast
  ring

theorem S_neg (w : V × (V →L[ℝ] ℝ)) (f : SchwartzMap V ℂ) : S w (S (-w) f) = f := by
  have := S_add w (-w) f
  rw [add_neg_cancel, S_zero] at this
  simpa using this.symm

theorem tendsto_S (f : SchwartzMap V ℂ) : Tendsto (fun w => S w f) (𝓝 0) (𝓝 f) := by
  rw [(schwartz_withSeminorms ℂ V ℂ).tendsto_nhds]
  intro i ε hε
  obtain ⟨p, -, hp⟩ := lip _ ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i)
  have h1 : Tendsto (fun w : V × (V →L[ℝ] ℝ) => ‖w‖ * p f) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_norm_zero (E := V × (V →L[ℝ] ℝ))).mul_const (p f)
  filter_upwards [h1.eventually (gt_mem_nhds hε), Metric.closedBall_mem_nhds 0 one_pos] with w h2 h3
  exact (hp w f (by simpa using h3)).trans_lt h2

theorem continuous_S (f : SchwartzMap V ℂ) : Continuous fun w => S w f := by
  refine continuous_iff_continuousAt.2 fun w => ?_
  have h1 : Tendsto (fun u => u - w) (𝓝 w) (𝓝 0) := by simpa using (continuous_sub_right w).tendsto w
  have h2 : Continuous fun h : V × (V →L[ℝ] ℝ) => cexp (I * ((w.2 h.1 - h.2 w.1) / 2 : ℝ)) := by fun_prop
  have h3 := ((h2.tendsto 0).smul (((S w).continuous.tendsto f).comp (tendsto_S f))).comp h1
  simp only [Prod.fst_zero, Prod.snd_zero, map_zero, ContinuousLinearMap.zero_apply, sub_self, zero_div, ofReal_zero, mul_zero,
    Complex.exp_zero, one_smul] at h3
  refine h3.congr fun u => ?_
  simp only [Function.comp_apply]
  rw [← S_add, add_sub_cancel]

theorem lip_pow (n : ℕ) : ∀ q : Seminorm ℂ (SchwartzMap V ℂ), Continuous q → ∃ p : Seminorm ℂ (SchwartzMap V ℂ),
    Continuous p ∧ ∀ w f, ‖w‖ ≤ 1 → q ((fun g => S w g - g)^[n] f) ≤ ‖w‖ ^ n * p f := by
  induction n with
  | zero => exact fun q hq => ⟨q, hq, fun w f _ => by simp⟩
  | succ n ih =>
    intro q hq
    obtain ⟨p, hp, h⟩ := ih q hq
    obtain ⟨p', hp', h'⟩ := lip p hp
    refine ⟨p', hp', fun w f hw => ?_⟩
    rw [Function.iterate_succ_apply, pow_succ, mul_assoc]
    exact (h w _ hw).trans (mul_le_mul_of_nonneg_left (h' w f hw) (by positivity))

theorem decay {Y Z : Type} [AddCommGroup Z] [Module ℂ Z] (A : Y → SchwartzMap V ℂ →ₗ[ℂ] Z) (s : Y → ℝ) (hs : ∀ y, 0 ≤ s y)
    (K : ℝ) (hK : ∀ y, 0 < s y → ∃ w, ‖w‖ * s y ≤ K ∧ ∀ f, A y (S w f) = -A y f) (q : Seminorm ℂ Z)
    (p : Seminorm ℂ (SchwartzMap V ℂ)) (hp : Continuous p) (M : ℕ) (hq : ∀ y f, q (A y f) ≤ (1 + s y) ^ M * p f) (N : ℕ) :
    ∃ p' : Seminorm ℂ (SchwartzMap V ℂ), Continuous p' ∧ ∀ y f, q (A y f) * (1 + s y) ^ N ≤ p' f := by
  obtain ⟨p₁, hp₁, h₁⟩ := lip_pow (M + N) p hp
  set R := max K 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  refine ⟨sc ((1 + R) ^ (M + N)) p + sc ((2 * R) ^ (M + N)) p₁,
    (sc_cont _ hp).add (sc_cont _ hp₁), fun y f => ?_⟩
  rw [Seminorm.add_apply, sc_apply (by positivity), sc_apply (by positivity)]
  have a1 := apply_nonneg p f
  have a2 := apply_nonneg p₁ f
  have a3 := hs y
  rcases le_total (s y) R with h | h
  · refine le_add_of_le_of_nonneg ?_ (by positivity)
    calc _ ≤ (1 + s y) ^ M * p f * (1 + s y) ^ N := mul_le_mul_of_nonneg_right (hq y f) (by positivity)
      _ = (1 + s y) ^ (M + N) * p f := by ring
      _ ≤ _ := by gcongr
  · refine le_add_of_nonneg_of_le (by positivity) ?_
    obtain ⟨w, hw, hA⟩ := hK y (by linarith)
    have hw' : ‖w‖ * s y ≤ R := hw.trans (le_max_left _ _)
    have hw1 : ‖w‖ ≤ 1 := by nlinarith [norm_nonneg w]
    have key : ∀ n : ℕ, ∀ g, q (A y g) ≤ q (A y ((fun g => S w g - g)^[n] g)) := fun n => by
      induction n with
      | zero => exact fun g => le_rfl
      | succ n ih =>
        intro g
        rw [Function.iterate_succ_apply]
        refine le_trans ?_ (ih _)
        rw [map_sub, hA, show -A y g - A y g = (-2 : ℂ) • A y g by module, map_smul_eq_mul]
        have := apply_nonneg q (A y g)
        simp only [norm_neg, Complex.norm_ofNat]
        linarith
    have h2 : ‖w‖ * (1 + s y) ≤ 2 * R := by nlinarith [norm_nonneg w]
    calc _ ≤ (1 + s y) ^ M * (‖w‖ ^ (M + N) * p₁ f) * (1 + s y) ^ N := mul_le_mul_of_nonneg_right
          ((key _ f).trans ((hq y _).trans (mul_le_mul_of_nonneg_left (h₁ w f hw1) (by positivity)))) (by positivity)
      _ = (‖w‖ * (1 + s y)) ^ (M + N) * p₁ f := by rw [mul_pow]; ring
      _ ≤ _ := by gcongr

theorem exists_half {U : Type} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] (b : U →ₗ[ℝ] U →L[ℝ] ℝ)
    (hb : ∀ x, b x = 0 → x = 0) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, x ≠ 0 → ∃ a, ‖a‖ * ‖x‖ ≤ K ∧ b x a = 1 / 2 := by
  obtain ⟨K, -, hK⟩ := b.exists_antilipschitzWith (LinearMap.ker_eq_bot'.2 hb)
  refine ⟨K, K.2, fun x hx => ?_⟩
  have h0 : 0 < ‖b x‖ := norm_pos_iff.2 fun h => hx (hb x h)
  obtain ⟨a, ha, ha'⟩ := (b x).exists_lt_apply_of_lt_opNorm (half_lt_self h0)
  have h1 : b x a ≠ 0 := norm_pos_iff.1 (by linarith)
  have h2 : ‖x‖ ≤ K * ‖b x‖ := by simpa using hK.le_mul_dist x 0
  refine ⟨(2 * b x a)⁻¹ • a, ?_, by rw [map_smul, smul_eq_mul]; field_simp⟩
  rw [norm_smul, norm_inv, norm_mul, Real.norm_two, mul_assoc, inv_mul_le_iff₀ (by linarith)]
  have := K.2
  nlinarith [norm_nonneg a, norm_nonneg x, mul_nonneg this (norm_nonneg (b x a))]

end PositivityTheory.ThKCT.Arch

end
