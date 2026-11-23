import Mathlib

noncomputable section

namespace PI.EF.Rect

open Complex MeasureTheory intervalIntegral Set Filter Topology Real

def rectInt (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I)

lemma continuousOn_hseg {f : ℂ → ℂ} {a₁ a₂ b : ℝ}
    (hc : ∀ x ∈ uIcc a₁ a₂, ContinuousAt f (x + b * I)) :
    ContinuousOn (fun x : ℝ => f (x + b * I)) (uIcc a₁ a₂) := by
  intro x hx
  exact (ContinuousAt.comp (f := fun t : ℝ => (t : ℂ) + b * I) (x := x) (hc x hx)
    (by fun_prop)).continuousWithinAt

lemma continuousOn_vseg {f : ℂ → ℂ} {a b₁ b₂ : ℝ}
    (hc : ∀ y ∈ uIcc b₁ b₂, ContinuousAt f (a + y * I)) :
    ContinuousOn (fun y : ℝ => f (a + y * I)) (uIcc b₁ b₂) := by
  intro y hy
  exact (ContinuousAt.comp (f := fun t : ℝ => (a : ℂ) + t * I) (x := y) (hc y hy)
    (by fun_prop)).continuousWithinAt

lemma hint_of_hasDerivAt {F f : ℂ → ℂ} {a₁ a₂ b : ℝ}
    (h : ∀ x ∈ uIcc a₁ a₂, HasDerivAt F (f (x + b * I)) (x + b * I))
    (hc : ∀ x ∈ uIcc a₁ a₂, ContinuousAt f (x + b * I)) :
    ∫ x : ℝ in a₁..a₂, f (x + b * I) = F (a₂ + b * I) - F (a₁ + b * I) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => F (x + b * I))
    (fun x hx => ?_) (continuousOn_hseg hc).intervalIntegrable
  have hg : HasDerivAt (fun t : ℝ => (t : ℂ) + b * I) 1 x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).add_const ((b : ℂ) * I)
  have hd := (h x hx).comp x hg
  rw [mul_one] at hd
  exact hd

lemma vint_of_hasDerivAt {F f : ℂ → ℂ} {a b₁ b₂ : ℝ}
    (h : ∀ y ∈ uIcc b₁ b₂, HasDerivAt F (f (a + y * I)) (a + y * I))
    (hc : ∀ y ∈ uIcc b₁ b₂, ContinuousAt f (a + y * I)) :
    I • ∫ y : ℝ in b₁..b₂, f (a + y * I) = F (a + b₂ * I) - F (a + b₁ * I) := by
  have hd : ∀ y ∈ uIcc b₁ b₂, HasDerivAt (fun t : ℝ => F (a + t * I)) (f (a + y * I) * I) y := by
    intro y hy
    have hg : HasDerivAt (fun t : ℝ => (a : ℂ) + t * I) I y := by
      simpa using (((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (a : ℂ)
    exact (h y hy).comp y hg
  rw [← intervalIntegral.integral_smul]
  have e : (fun y : ℝ => I • f (a + y * I)) = fun y : ℝ => f (a + y * I) * I := by
    funext y
    rw [smul_eq_mul, mul_comm]
  rw [e]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuousOn_vseg hc).mul continuousOn_const).intervalIntegrable

def rectBdry (z w : ℂ) : Set ℂ :=
  {s | (s.re ∈ uIcc z.re w.re ∧ (s.im = z.im ∨ s.im = w.im)) ∨
       (s.im ∈ uIcc z.im w.im ∧ (s.re = z.re ∨ s.re = w.re))}

lemma hseg_mem_bdry_bot {z w : ℂ} {x : ℝ} (hx : x ∈ uIcc z.re w.re) :
    ((x : ℂ) + z.im * I) ∈ rectBdry z w := by
  simp only [rectBdry, Set.mem_ofPred_eq]
  exact Or.inl ⟨by simpa using hx, Or.inl (by simp)⟩

lemma hseg_mem_bdry_top {z w : ℂ} {x : ℝ} (hx : x ∈ uIcc z.re w.re) :
    ((x : ℂ) + w.im * I) ∈ rectBdry z w := by
  simp only [rectBdry, Set.mem_ofPred_eq]
  exact Or.inl ⟨by simpa using hx, Or.inr (by simp)⟩

lemma vseg_mem_bdry_left {z w : ℂ} {y : ℝ} (hy : y ∈ uIcc z.im w.im) :
    ((z.re : ℂ) + y * I) ∈ rectBdry z w := by
  simp only [rectBdry, Set.mem_ofPred_eq]
  exact Or.inr ⟨by simpa using hy, Or.inl (by simp)⟩

lemma vseg_mem_bdry_right {z w : ℂ} {y : ℝ} (hy : y ∈ uIcc z.im w.im) :
    ((w.re : ℂ) + y * I) ∈ rectBdry z w := by
  simp only [rectBdry, Set.mem_ofPred_eq]
  exact Or.inr ⟨by simpa using hy, Or.inr (by simp)⟩

theorem rectInt_eq_zero_of_primitive {F f : ℂ → ℂ} {z w : ℂ}
    (h : ∀ s ∈ rectBdry z w, HasDerivAt F (f s) s) (hc : ∀ s ∈ rectBdry z w, ContinuousAt f s) :
    rectInt f z w = 0 := by
  unfold rectInt
  rw [hint_of_hasDerivAt (fun x hx => h _ (hseg_mem_bdry_bot hx)) (fun x hx => hc _ (hseg_mem_bdry_bot hx)),
    hint_of_hasDerivAt (fun x hx => h _ (hseg_mem_bdry_top hx)) (fun x hx => hc _ (hseg_mem_bdry_top hx)),
    vint_of_hasDerivAt (fun y hy => h _ (vseg_mem_bdry_right hy)) (fun y hy => hc _ (vseg_mem_bdry_right hy)),
    vint_of_hasDerivAt (fun y hy => h _ (vseg_mem_bdry_left hy)) (fun y hy => hc _ (vseg_mem_bdry_left hy))]
  ring

def rectOpen (z w : ℂ) : Set ℂ := {s | z.re < s.re ∧ s.re < w.re ∧ z.im < s.im ∧ s.im < w.im}

def rectClosed (z w : ℂ) : Set ℂ := Icc z.re w.re ×ℂ Icc z.im w.im

lemma ne_of_mem_bdry_of_mem_open {z w s p : ℂ} (hs : s ∈ rectBdry z w) (hp : p ∈ rectOpen z w) :
    s ≠ p := by
  rintro rfl
  obtain ⟨h1, h2, h3, h4⟩ := hp
  rcases hs with ⟨-, h | h⟩ | ⟨-, h | h⟩ <;> linarith

theorem rectInt_inv_sub_sq {z w p : ℂ} (hp : p ∈ rectOpen z w) :
    rectInt (fun s => ((s - p) ^ 2)⁻¹) z w = 0 := by
  apply rectInt_eq_zero_of_primitive (F := fun s => -(s - p)⁻¹)
  · intro s hs
    have hne : s - p ≠ 0 := sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)
    have hd := ((hasDerivAt_inv hne).comp_sub_const s p).neg
    rw [neg_neg] at hd
    exact hd
  · intro s hs
    have hne : s - p ≠ 0 := sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)
    exact ContinuousAt.inv₀ (by fun_prop) (pow_ne_zero 2 hne)

lemma log_sub_log_neg_of_im_pos {a : ℂ} (ha : 0 < a.im) : Complex.log a - Complex.log (-a) = π * I := by
  have h := Complex.arg_neg_eq_arg_sub_pi_of_im_pos ha
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, h]

lemma log_neg_sub_log_of_im_neg {b : ℂ} (hb : b.im < 0) : Complex.log (-b) - Complex.log b = π * I := by
  have h := Complex.arg_neg_eq_arg_add_pi_of_im_neg hb
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, h]

theorem rectInt_inv_sub {z w p : ℂ} (hp : p ∈ rectOpen z w) :
    rectInt (fun s => (s - p)⁻¹) z w = 2 * π * I := by
  obtain ⟨h1, h2, h3, h4⟩ := id hp
  have hcont : ∀ s ∈ rectBdry z w, ContinuousAt (fun s => (s - p)⁻¹) s := fun s hs =>
    ContinuousAt.inv₀ (by fun_prop) (sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp))
  have hL : ∀ s, s - p ∈ slitPlane → HasDerivAt (fun s => Complex.log (s - p)) ((s - p)⁻¹) s := by
    intro s hs
    simpa using ((hasDerivAt_id s).sub_const p).clog hs
  have hM : ∀ s, p - s ∈ slitPlane → HasDerivAt (fun s => Complex.log (p - s)) ((s - p)⁻¹) s := by
    intro s hs
    convert ((hasDerivAt_id s).const_sub p).clog hs using 1
    simp only [id_eq]
    rw [neg_div, ← div_neg, neg_sub, one_div]
    rfl
  unfold rectInt
  rw [hint_of_hasDerivAt (F := fun s => Complex.log (s - p)) (f := fun s => (s - p)⁻¹)
      (a₁ := z.re) (a₂ := w.re) (b := z.im)
      (fun x _ => hL _ (mem_slitPlane_iff.2 (Or.inr (by intro h; simp at h; linarith))))
      (fun x hx => hcont _ (hseg_mem_bdry_bot hx)),
    hint_of_hasDerivAt (F := fun s => Complex.log (s - p)) (f := fun s => (s - p)⁻¹)
      (a₁ := z.re) (a₂ := w.re) (b := w.im)
      (fun x _ => hL _ (mem_slitPlane_iff.2 (Or.inr (by intro h; simp at h; linarith))))
      (fun x hx => hcont _ (hseg_mem_bdry_top hx)),
    vint_of_hasDerivAt (F := fun s => Complex.log (s - p)) (f := fun s => (s - p)⁻¹)
      (a := w.re) (b₁ := z.im) (b₂ := w.im)
      (fun y _ => hL _ (mem_slitPlane_iff.2 (Or.inl (by simp; linarith))))
      (fun y hy => hcont _ (vseg_mem_bdry_right hy)),
    vint_of_hasDerivAt (F := fun s => Complex.log (p - s)) (f := fun s => (s - p)⁻¹)
      (a := z.re) (b₁ := z.im) (b₂ := w.im)
      (fun y _ => hM _ (mem_slitPlane_iff.2 (Or.inl (by simp; linarith))))
      (fun y hy => hcont _ (vseg_mem_bdry_left hy))]
  have e1 := log_sub_log_neg_of_im_pos (a := (z.re : ℂ) + w.im * I - p) (by simp; linarith)
  have e2 := log_neg_sub_log_of_im_neg (b := (z.re : ℂ) + z.im * I - p) (by simp; linarith)
  rw [neg_sub] at e1 e2
  beta_reduce
  linear_combination e1 + e2

lemma sides_integrable {f : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f (rectBdry z w)) :
    IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hf.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + z.im * I).continuousOn
      fun x hx => hseg_mem_bdry_bot hx).intervalIntegrable
  · exact (hf.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + w.im * I).continuousOn
      fun x hx => hseg_mem_bdry_top hx).intervalIntegrable
  · exact (hf.comp (by fun_prop : Continuous fun y : ℝ => (w.re : ℂ) + y * I).continuousOn
      fun y hy => vseg_mem_bdry_right hy).intervalIntegrable
  · exact (hf.comp (by fun_prop : Continuous fun y : ℝ => (z.re : ℂ) + y * I).continuousOn
      fun y hy => vseg_mem_bdry_left hy).intervalIntegrable

lemma rectInt_congr {f g : ℂ → ℂ} {z w : ℂ} (h : EqOn f g (rectBdry z w)) :
    rectInt f z w = rectInt g z w := by
  unfold rectInt
  rw [intervalIntegral.integral_congr (fun x hx => h (hseg_mem_bdry_bot hx)),
    intervalIntegral.integral_congr (fun x hx => h (hseg_mem_bdry_top hx)),
    intervalIntegral.integral_congr (fun y hy => h (vseg_mem_bdry_right hy)),
    intervalIntegral.integral_congr (fun y hy => h (vseg_mem_bdry_left hy))]

lemma rectInt_add {f g : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f (rectBdry z w))
    (hg : ContinuousOn g (rectBdry z w)) :
    rectInt (fun s => f s + g s) z w = rectInt f z w + rectInt g z w := by
  obtain ⟨f1, f2, f3, f4⟩ := sides_integrable hf
  obtain ⟨g1, g2, g3, g4⟩ := sides_integrable hg
  unfold rectInt
  beta_reduce
  rw [intervalIntegral.integral_add f1 g1, intervalIntegral.integral_add f2 g2,
    intervalIntegral.integral_add f3 g3, intervalIntegral.integral_add f4 g4]
  simp only [smul_eq_mul]
  ring

lemma rectInt_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectInt (fun s => c * f s) z w = c * rectInt f z w := by
  unfold rectInt
  beta_reduce
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

lemma rectInt_zero (z w : ℂ) : rectInt (fun _ => 0) z w = 0 := by
  unfold rectInt
  simp

lemma rectInt_finset_sum {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ) {z w : ℂ}
    (hF : ∀ i ∈ S, ContinuousOn (F i) (rectBdry z w)) :
    rectInt (fun s => ∑ i ∈ S, F i s) z w = ∑ i ∈ S, rectInt (F i) z w := by
  classical
  revert hF
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact rectInt_zero z w
  · intro a S ha ih hF
    simp only [Finset.sum_insert ha]
    rw [rectInt_add (hF a (Finset.mem_insert_self a S))
      (continuousOn_finsetSum _ fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))]

lemma mem_rectClosed {z w s : ℂ} :
    s ∈ rectClosed z w ↔ (z.re ≤ s.re ∧ s.re ≤ w.re) ∧ (z.im ≤ s.im ∧ s.im ≤ w.im) := by
  simp [rectClosed, Complex.mem_reProdIm]

lemma rectOpen_eq (z w : ℂ) : rectOpen z w = Ioo z.re w.re ×ℂ Ioo z.im w.im := by
  ext s
  simp [rectOpen, Complex.mem_reProdIm, and_assoc]

lemma rectClosed_mem_nhds {z w p : ℂ} (hp : p ∈ rectOpen z w) : rectClosed z w ∈ 𝓝 p := by
  have ho : IsOpen (rectOpen z w) := by
    rw [rectOpen_eq]
    exact isOpen_Ioo.reProdIm isOpen_Ioo
  refine Filter.mem_of_superset (ho.mem_nhds hp) fun s hs => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hs
  exact mem_rectClosed.2 ⟨⟨h1.le, h2.le⟩, h3.le, h4.le⟩

lemma rectBdry_subset {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im) :
    rectBdry z w ⊆ rectClosed z w := by
  intro s hs
  rw [mem_rectClosed]
  rcases hs with ⟨hr, hi⟩ | ⟨hi, hr⟩
  · rw [uIcc_of_le hre, Set.mem_Icc] at hr
    rcases hi with hi | hi <;> exact ⟨hr, by constructor <;> linarith⟩
  · rw [uIcc_of_le him, Set.mem_Icc] at hi
    rcases hr with hr | hr <;> exact ⟨by constructor <;> linarith, hi⟩

lemma le_of_mem_rectOpen {z w p : ℂ} (hp : p ∈ rectOpen z w) : z.re ≤ w.re ∧ z.im ≤ w.im := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  exact ⟨by linarith, by linarith⟩

theorem rectInt_eq_zero_of_differentiableOn {f : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (hf : DifferentiableOn ℂ f (rectClosed z w)) : rectInt f z w = 0 := by
  have e : rectClosed z w = uIcc z.re w.re ×ℂ uIcc z.im w.im := by
    rw [rectClosed, uIcc_of_le hre, uIcc_of_le him]
  rw [e] at hf
  unfold rectInt
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hf

lemma continuousOn_div_sub {h : ℂ → ℂ} {z w p : ℂ} (hp : p ∈ rectOpen z w)
    (hh : ContinuousOn h (rectBdry z w)) : ContinuousOn (fun s => h s / (s - p)) (rectBdry z w) :=
  hh.div (continuousOn_id.sub continuousOn_const) fun s hs =>
    sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)

lemma continuousOn_div_sub_sq {h : ℂ → ℂ} {z w p : ℂ} (hp : p ∈ rectOpen z w)
    (hh : ContinuousOn h (rectBdry z w)) :
    ContinuousOn (fun s => h s / (s - p) ^ 2) (rectBdry z w) :=
  hh.div ((continuousOn_id.sub continuousOn_const).pow 2) fun s hs =>
    pow_ne_zero 2 (sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp))

lemma continuousOn_bdry {h : ℂ → ℂ} {z w p : ℂ} (hp : p ∈ rectOpen z w)
    (hh : DifferentiableOn ℂ h (rectClosed z w)) : ContinuousOn h (rectBdry z w) :=
  hh.continuousOn.mono (rectBdry_subset (le_of_mem_rectOpen hp).1 (le_of_mem_rectOpen hp).2)

theorem rectInt_div_sub {h : ℂ → ℂ} {z w p : ℂ} (hp : p ∈ rectOpen z w)
    (hh : DifferentiableOn ℂ h (rectClosed z w)) :
    rectInt (fun s => h s / (s - p)) z w = 2 * π * I * h p := by
  obtain ⟨hre, him⟩ := le_of_mem_rectOpen hp
  have hN := rectClosed_mem_nhds hp
  have hsub := rectBdry_subset hre him
  have hdc : ContinuousOn (dslope h p) (rectClosed z w) :=
    (continuousOn_dslope hN).2 ⟨hh.continuousOn, hh.differentiableAt hN⟩
  have hz : rectInt (dslope h p) z w = 0 := by
    have e : rectClosed z w = uIcc z.re w.re ×ℂ uIcc z.im w.im := by
      rw [rectClosed, uIcc_of_le hre, uIcc_of_le him]
    unfold rectInt
    refine Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable _ z w {p}
      (Set.countable_singleton p) (e ▸ hdc) ?_
    intro x hx
    rw [min_eq_left hre, max_eq_right hre, min_eq_left him, max_eq_right him] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hxo : x ∈ rectOpen z w := by
      rw [rectOpen_eq]
      exact hx1
    exact (differentiableAt_dslope_of_ne hx2).2 (hh.differentiableAt (rectClosed_mem_nhds hxo))
  have hinv : ContinuousOn (fun s => h p * (s - p)⁻¹) (rectBdry z w) :=
    continuousOn_const.mul (ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun s hs =>
      sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp))
  have hcong : EqOn (fun s => h s / (s - p)) (fun s => dslope h p s + h p * (s - p)⁻¹)
      (rectBdry z w) := by
    intro s hs
    have hne : s - p ≠ 0 := sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)
    simp only
    rw [dslope_of_ne _ (sub_ne_zero.1 hne), slope_def_field, div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [rectInt_congr hcong, rectInt_add (hdc.mono hsub) hinv, hz, rectInt_const_mul,
    rectInt_inv_sub hp]
  ring

theorem rectInt_div_sub_sq {h : ℂ → ℂ} {z w p : ℂ} (hp : p ∈ rectOpen z w)
    (hh : DifferentiableOn ℂ h (rectClosed z w)) :
    rectInt (fun s => h s / (s - p) ^ 2) z w = 2 * π * I * deriv h p := by
  obtain ⟨hre, him⟩ := le_of_mem_rectOpen hp
  have hN := rectClosed_mem_nhds hp
  have hsub := rectBdry_subset hre him
  have hd : DifferentiableOn ℂ (dslope h p) (rectClosed z w) :=
    (Complex.differentiableOn_dslope hN).2 hh
  have hinv : ContinuousOn (fun s => h p * ((s - p) ^ 2)⁻¹) (rectBdry z w) :=
    continuousOn_const.mul (ContinuousOn.inv₀ ((continuousOn_id.sub continuousOn_const).pow 2)
      fun s hs => pow_ne_zero 2 (sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)))
  have hcong : EqOn (fun s => h s / (s - p) ^ 2)
      (fun s => dslope h p s / (s - p) + h p * ((s - p) ^ 2)⁻¹) (rectBdry z w) := by
    intro s hs
    have hne : s - p ≠ 0 := sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)
    simp only
    rw [dslope_of_ne _ (sub_ne_zero.1 hne), slope_def_field, div_div, ← sq, div_eq_mul_inv,
      div_eq_mul_inv]
    ring
  rw [rectInt_congr hcong, rectInt_add (continuousOn_div_sub hp (hd.continuousOn.mono hsub)) hinv,
    rectInt_div_sub hp hd, rectInt_const_mul, rectInt_inv_sub_sq hp, dslope_same]
  ring

theorem rect_residue_gen {z w : ℂ} {H E : ℂ → ℂ} (Z : Finset ℂ) (wt : ℂ → ℂ) (e : ℂ)
    (h0 : (0 : ℂ) ∈ rectOpen z w) (hH : DifferentiableOn ℂ H (rectClosed z w))
    (hE : DifferentiableOn ℂ E (rectClosed z w)) (hZ : ∀ ρ ∈ Z, ρ ≠ 0 ∧ ρ ∈ rectOpen z w) :
    rectInt (fun s => (H s + (∑ ρ ∈ Z, wt ρ / (s - ρ)) + e / s) * (E s / s)) z w =
      2 * π * I * (H 0 * E 0 + (∑ ρ ∈ Z, wt ρ * ((E ρ - E 0) / ρ)) + e * deriv E 0) := by
  obtain ⟨hre, him⟩ := le_of_mem_rectOpen h0
  have hsub := rectBdry_subset hre him
  have hEb : ContinuousOn E (rectBdry z w) := hE.continuousOn.mono hsub
  have hA : ContinuousOn (fun s => H s * E s / (s - 0)) (rectBdry z w) :=
    continuousOn_div_sub h0 ((hH.mul hE).continuousOn.mono hsub)
  have hT : ∀ ρ ∈ Z, ContinuousOn
      (fun s => wt ρ / ρ * (E s / (s - ρ)) + -(wt ρ / ρ) * (E s / (s - 0))) (rectBdry z w) :=
    fun ρ hρ => (continuousOn_const.mul (continuousOn_div_sub (hZ ρ hρ).2 hEb)).add
      (continuousOn_const.mul (continuousOn_div_sub h0 hEb))
  have hB : ContinuousOn
      (fun s => ∑ ρ ∈ Z, (wt ρ / ρ * (E s / (s - ρ)) + -(wt ρ / ρ) * (E s / (s - 0))))
      (rectBdry z w) := continuousOn_finsetSum _ hT
  have hC : ContinuousOn (fun s => e * (E s / (s - 0) ^ 2)) (rectBdry z w) :=
    continuousOn_const.mul (continuousOn_div_sub_sq h0 hEb)
  have hcong : EqOn (fun s => (H s + (∑ ρ ∈ Z, wt ρ / (s - ρ)) + e / s) * (E s / s))
      (fun s => H s * E s / (s - 0) +
        (∑ ρ ∈ Z, (wt ρ / ρ * (E s / (s - ρ)) + -(wt ρ / ρ) * (E s / (s - 0)))) +
        e * (E s / (s - 0) ^ 2)) (rectBdry z w) := by
    intro s hs
    have hs0 : s ≠ 0 := ne_of_mem_bdry_of_mem_open hs h0
    simp only [sub_zero]
    rw [add_mul, add_mul, Finset.sum_mul]
    have hterm : ∀ ρ ∈ Z, wt ρ / (s - ρ) * (E s / s) =
        wt ρ / ρ * (E s / (s - ρ)) + -(wt ρ / ρ) * (E s / s) := by
      intro ρ hρ
      have hρ0 := (hZ ρ hρ).1
      have hsρ : s - ρ ≠ 0 := sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs (hZ ρ hρ).2)
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm]
    congr 1
    · rw [mul_div_assoc]
    · rw [div_mul_div_comm, ← sq, mul_div_assoc]
  have hsum : ∀ ρ ∈ Z, rectInt (fun s => wt ρ / ρ * (E s / (s - ρ)) + -(wt ρ / ρ) * (E s / (s - 0))) z w =
      2 * π * I * (wt ρ * ((E ρ - E 0) / ρ)) := by
    intro ρ hρ
    rw [rectInt_add (f := fun s => wt ρ / ρ * (E s / (s - ρ))) (g := fun s => -(wt ρ / ρ) * (E s / (s - 0)))
      (continuousOn_const.mul (continuousOn_div_sub (hZ ρ hρ).2 hEb))
      (continuousOn_const.mul (continuousOn_div_sub h0 hEb)), rectInt_const_mul, rectInt_const_mul,
      rectInt_div_sub (hZ ρ hρ).2 hE, rectInt_div_sub h0 hE]
    ring
  rw [rectInt_congr hcong,
    rectInt_add (f := fun s => H s * E s / (s - 0) +
        ∑ ρ ∈ Z, (wt ρ / ρ * (E s / (s - ρ)) + -(wt ρ / ρ) * (E s / (s - 0))))
      (g := fun s => e * (E s / (s - 0) ^ 2)) (hA.add hB) hC,
    rectInt_add (f := fun s => H s * E s / (s - 0))
      (g := fun s => ∑ ρ ∈ Z, (wt ρ / ρ * (E s / (s - ρ)) + -(wt ρ / ρ) * (E s / (s - 0)))) hA hB, rectInt_finset_sum Z _ hT,
    rectInt_div_sub (h := fun s => H s * E s) h0 (hH.mul hE), rectInt_const_mul, rectInt_div_sub_sq h0 hE,
    Finset.sum_congr rfl hsum, ← Finset.mul_sum]
  ring

theorem rect_residue {z w : ℂ} {H : ℂ → ℂ} (Z : Finset ℂ) (wt : ℂ → ℂ) (e : ℂ) {u : ℝ} (hu : 0 < u)
    (h0 : (0 : ℂ) ∈ rectOpen z w) (hH : DifferentiableOn ℂ H (rectClosed z w))
    (hZ : ∀ ρ ∈ Z, ρ ≠ 0 ∧ ρ ∈ rectOpen z w) :
    rectInt (fun s => (H s + (∑ ρ ∈ Z, wt ρ / (s - ρ)) + e / s) * ((u : ℂ) ^ s / s)) z w =
      2 * π * I * (H 0 + (∑ ρ ∈ Z, wt ρ * (((u : ℂ) ^ ρ - 1) / ρ)) + e * Real.log u) := by
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.2 hu.ne'
  have hd : ∀ s : ℂ, HasDerivAt (fun s : ℂ => (u : ℂ) ^ s) ((u : ℂ) ^ s * Complex.log u) s :=
    fun s => (hasStrictDerivAt_const_cpow (Or.inl hu0)).hasDerivAt
  have hE : DifferentiableOn ℂ (fun s : ℂ => (u : ℂ) ^ s) (rectClosed z w) :=
    fun s _ => (hd s).differentiableAt.differentiableWithinAt
  rw [rect_residue_gen Z wt e h0 hH hE hZ]
  beta_reduce
  rw [(hd 0).deriv, ofReal_log hu.le]
  simp only [cpow_zero, mul_one, one_mul]

end PI.EF.Rect
