import Mathlib

open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def rectIntegral (f : ℂ → E) (z w : ℂ) : E :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

def rectBoundary (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ [[z.re, w.re]] ×ℂ {w.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    {w.re} ×ℂ [[z.im, w.im]]

section Edges

variable {z w : ℂ}

lemma bottom_mem_rectBoundary {x : ℝ} (hx : x ∈ [[z.re, w.re]]) :
    (x : ℂ) + z.im * I ∈ rectBoundary z w := by
  simp [rectBoundary, mem_reProdIm, hx]

lemma top_mem_rectBoundary {x : ℝ} (hx : x ∈ [[z.re, w.re]]) :
    (x : ℂ) + w.im * I ∈ rectBoundary z w := by
  simp [rectBoundary, mem_reProdIm, hx]

lemma right_mem_rectBoundary {y : ℝ} (hy : y ∈ [[z.im, w.im]]) :
    (w.re : ℂ) + y * I ∈ rectBoundary z w := by
  simp [rectBoundary, mem_reProdIm, hy]

lemma left_mem_rectBoundary {y : ℝ} (hy : y ∈ [[z.im, w.im]]) :
    (z.re : ℂ) + y * I ∈ rectBoundary z w := by
  simp [rectBoundary, mem_reProdIm, hy]

lemma rectBoundary_subset : rectBoundary z w ⊆ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := by
  intro u hu
  simp only [rectBoundary, mem_union, mem_reProdIm, mem_singleton_iff] at hu ⊢
  rcases hu with ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · exact ⟨h1, h2 ▸ left_mem_uIcc⟩
  · exact ⟨h1, h2 ▸ right_mem_uIcc⟩
  · exact ⟨h1 ▸ left_mem_uIcc, h2⟩
  · exact ⟨h1 ▸ right_mem_uIcc, h2⟩

lemma notMem_rectBoundary_of_mem_Ioo {p : ℂ}
    (hre : p.re ∈ Ioo (min z.re w.re) (max z.re w.re))
    (him : p.im ∈ Ioo (min z.im w.im) (max z.im w.im)) : p ∉ rectBoundary z w := by
  simp only [rectBoundary, mem_union, mem_reProdIm, mem_singleton_iff, not_or, not_and]
  have key : ∀ {a b t : ℝ}, t ∈ Ioo (min a b) (max a b) → t ≠ a ∧ t ≠ b := by
    intro a b t ht
    obtain ⟨h1, h2⟩ := ht
    rw [min_lt_iff] at h1
    rw [lt_max_iff] at h2
    constructor <;> rintro rfl <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> linarith
  refine ⟨⟨⟨fun _ h ↦ (key him).1 h, fun _ h ↦ (key him).2 h⟩, fun h _ ↦ (key hre).1 h⟩,
    fun h _ ↦ (key hre).2 h⟩

variable {f g : ℂ → E}

omit [NormedSpace ℂ E] in
lemma intervalIntegrable_bottom (hf : ContinuousOn f (rectBoundary z w)) :
    IntervalIntegrable (fun x : ℝ ↦ f (x + z.im * I)) volume z.re w.re :=
  (hf.comp (by fun_prop : Continuous fun x : ℝ ↦ (x : ℂ) + z.im * I).continuousOn
    fun _ hx ↦ bottom_mem_rectBoundary hx).intervalIntegrable

omit [NormedSpace ℂ E] in
lemma intervalIntegrable_top (hf : ContinuousOn f (rectBoundary z w)) :
    IntervalIntegrable (fun x : ℝ ↦ f (x + w.im * I)) volume z.re w.re :=
  (hf.comp (by fun_prop : Continuous fun x : ℝ ↦ (x : ℂ) + w.im * I).continuousOn
    fun _ hx ↦ top_mem_rectBoundary hx).intervalIntegrable

omit [NormedSpace ℂ E] in
lemma intervalIntegrable_right (hf : ContinuousOn f (rectBoundary z w)) :
    IntervalIntegrable (fun y : ℝ ↦ f (w.re + y * I)) volume z.im w.im :=
  (hf.comp (by fun_prop : Continuous fun y : ℝ ↦ (w.re : ℂ) + y * I).continuousOn
    fun _ hy ↦ right_mem_rectBoundary hy).intervalIntegrable

omit [NormedSpace ℂ E] in
lemma intervalIntegrable_left (hf : ContinuousOn f (rectBoundary z w)) :
    IntervalIntegrable (fun y : ℝ ↦ f (z.re + y * I)) volume z.im w.im :=
  (hf.comp (by fun_prop : Continuous fun y : ℝ ↦ (z.re : ℂ) + y * I).continuousOn
    fun _ hy ↦ left_mem_rectBoundary hy).intervalIntegrable

end Edges

section Linearity

variable {z w : ℂ} {f g : ℂ → E}

theorem rectIntegral_add (hf : ContinuousOn f (rectBoundary z w))
    (hg : ContinuousOn g (rectBoundary z w)) :
    rectIntegral (fun u ↦ f u + g u) z w = rectIntegral f z w + rectIntegral g z w := by
  simp only [rectIntegral]
  rw [integral_add (intervalIntegrable_bottom hf) (intervalIntegrable_bottom hg),
    integral_add (intervalIntegrable_top hf) (intervalIntegrable_top hg),
    integral_add (intervalIntegrable_right hf) (intervalIntegrable_right hg),
    integral_add (intervalIntegrable_left hf) (intervalIntegrable_left hg)]
  simp only [smul_add]
  abel

theorem rectIntegral_sub (hf : ContinuousOn f (rectBoundary z w))
    (hg : ContinuousOn g (rectBoundary z w)) :
    rectIntegral (fun u ↦ f u - g u) z w = rectIntegral f z w - rectIntegral g z w := by
  simp only [rectIntegral]
  rw [integral_sub (intervalIntegrable_bottom hf) (intervalIntegrable_bottom hg),
    integral_sub (intervalIntegrable_top hf) (intervalIntegrable_top hg),
    integral_sub (intervalIntegrable_right hf) (intervalIntegrable_right hg),
    integral_sub (intervalIntegrable_left hf) (intervalIntegrable_left hg)]
  simp only [smul_sub]
  abel

theorem rectIntegral_neg : rectIntegral (fun u ↦ -f u) z w = -rectIntegral f z w := by
  simp only [rectIntegral, intervalIntegral.integral_neg, smul_neg]
  abel

theorem rectIntegral_smul (c : ℂ) : rectIntegral (fun u ↦ c • f u) z w = c • rectIntegral f z w := by
  simp only [rectIntegral, intervalIntegral.integral_smul, smul_sub, smul_add]
  rw [smul_comm I c, smul_comm I c]

theorem rectIntegral_const_mul {f : ℂ → ℂ} (c : ℂ) :
    rectIntegral (fun u ↦ c * f u) z w = c * rectIntegral f z w :=
  rectIntegral_smul (f := f) c

theorem rectIntegral_zero : rectIntegral (fun _ ↦ (0 : E)) z w = 0 := by
  simp [rectIntegral]

theorem rectIntegral_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → E}
    (hf : ∀ i ∈ s, ContinuousOn (f i) (rectBoundary z w)) :
    rectIntegral (fun u ↦ ∑ i ∈ s, f i u) z w = ∑ i ∈ s, rectIntegral (f i) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rectIntegral_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [rectIntegral_add (hf a (Finset.mem_insert_self a s))
      (continuousOn_finsetSum _ fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

theorem rectIntegral_congr (h : EqOn f g (rectBoundary z w)) :
    rectIntegral f z w = rectIntegral g z w := by
  simp only [rectIntegral]
  rw [integral_congr (g := fun x : ℝ ↦ g (x + z.im * I))
      fun x hx ↦ h (bottom_mem_rectBoundary hx),
    integral_congr (g := fun x : ℝ ↦ g (x + w.im * I)) fun x hx ↦ h (top_mem_rectBoundary hx),
    integral_congr (g := fun y : ℝ ↦ g (w.re + y * I)) fun y hy ↦ h (right_mem_rectBoundary hy),
    integral_congr (g := fun y : ℝ ↦ g (z.re + y * I)) fun y hy ↦ h (left_mem_rectBoundary hy)]

end Linearity

section Derivative

variable {z w : ℂ}

theorem rectIntegral_eq_zero_of_hasDerivAt [CompleteSpace E] {F f : ℂ → E}
    (hF : ∀ u ∈ rectBoundary z w, HasDerivAt F (f u) u) (hf : ContinuousOn f (rectBoundary z w)) :
    rectIntegral f z w = 0 := by
  have hh : ∀ c : ℝ, ∀ x : ℝ, (x : ℂ) + c * I ∈ rectBoundary z w →
      HasDerivAt (fun x : ℝ ↦ F (x + c * I)) (f (x + c * I)) x := by
    intro c x hx
    have h1 : HasDerivAt (fun y : ℝ ↦ (y : ℂ) + c * I) 1 x := by
      simpa using (hasDerivAt_id' x).ofReal_comp.add_const ((c : ℂ) * I)
    have h2 := (hF _ hx).scomp x h1
    rw [one_smul] at h2
    exact h2
  have hv : ∀ c : ℝ, ∀ y : ℝ, (c : ℂ) + y * I ∈ rectBoundary z w →
      HasDerivAt (fun y : ℝ ↦ F (c + y * I)) (I • f (c + y * I)) y := by
    intro c y hy
    have h1 : HasDerivAt (fun y : ℝ ↦ (c : ℂ) + y * I) I y := by
      simpa using ((hasDerivAt_id' y).ofReal_comp.mul_const I).const_add (c : ℂ)
    exact (hF _ hy).scomp y h1
  have hb : ∫ x : ℝ in z.re..w.re, f (x + z.im * I) =
      F (w.re + z.im * I) - F (z.re + z.im * I) :=
    integral_eq_sub_of_hasDerivAt (fun x hx ↦ hh _ x (bottom_mem_rectBoundary hx))
      (intervalIntegrable_bottom hf)
  have ht : ∫ x : ℝ in z.re..w.re, f (x + w.im * I) =
      F (w.re + w.im * I) - F (z.re + w.im * I) :=
    integral_eq_sub_of_hasDerivAt (fun x hx ↦ hh _ x (top_mem_rectBoundary hx))
      (intervalIntegrable_top hf)
  have hr : I • ∫ y : ℝ in z.im..w.im, f (w.re + y * I) =
      F (w.re + w.im * I) - F (w.re + z.im * I) := by
    rw [← intervalIntegral.integral_smul]
    exact integral_eq_sub_of_hasDerivAt (fun y hy ↦ hv _ y (right_mem_rectBoundary hy))
      ((intervalIntegrable_right hf).smul I)
  have hl : I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I) =
      F (z.re + w.im * I) - F (z.re + z.im * I) := by
    rw [← intervalIntegral.integral_smul]
    exact integral_eq_sub_of_hasDerivAt (fun y hy ↦ hv _ y (left_mem_rectBoundary hy))
      ((intervalIntegrable_left hf).smul I)
  rw [rectIntegral, hb, ht, hr, hl]
  abel

theorem rectIntegral_zpow_sub {p : ℂ} {n : ℤ} (hn : n ≠ -1) (hp : p ∉ rectBoundary z w) :
    rectIntegral (fun u ↦ (u - p) ^ n) z w = 0 := by
  have hn' : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hup : ∀ u ∈ rectBoundary z w, u - p ≠ 0 := fun u hu h ↦ hp (sub_eq_zero.1 h ▸ hu)
  refine rectIntegral_eq_zero_of_hasDerivAt (F := fun u ↦ (u - p) ^ (n + 1) / ((n : ℂ) + 1))
    (fun u hu ↦ ?_) ?_
  · have h1 : HasDerivAt (fun u : ℂ ↦ u - p) 1 u := (hasDerivAt_id u).sub_const p
    have h2 := ((hasDerivAt_zpow (n + 1) (u - p) (Or.inl (hup u hu))).comp u h1).div_const
      ((n : ℂ) + 1)
    refine h2.congr_deriv ?_
    rw [add_sub_cancel_right]
    push_cast
    field_simp
  · exact continuousOn_of_forall_continuousAt fun u hu ↦
      ((continuousAt_id.sub continuousAt_const).zpow₀ n (Or.inl (hup u hu)))

end Derivative

section Inverse

def invPrimitive (c x : ℝ) : ℂ :=
  ((Real.log (x ^ 2 + c ^ 2) / 2 : ℝ) : ℂ) - I * ((Real.arctan (x / c) : ℝ) : ℂ)

lemma ofReal_add_mul_I_ne_zero {c : ℝ} (hc : c ≠ 0) (x : ℝ) : (x : ℂ) + c * I ≠ 0 := by
  intro h
  apply hc
  simpa using congrArg Complex.im h

lemma hasDerivAt_invPrimitive {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (invPrimitive c) ((x : ℂ) + c * I)⁻¹ x := by
  have hpos : 0 < x ^ 2 + c ^ 2 := by positivity
  have h1 : HasDerivAt (fun x : ℝ ↦ Real.log (x ^ 2 + c ^ 2) / 2) (x / (x ^ 2 + c ^ 2)) x := by
    have := (((hasDerivAt_pow 2 x).add_const (c ^ 2)).log hpos.ne').div_const 2
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have h2 : HasDerivAt (fun x : ℝ ↦ Real.arctan (x / c)) (c / (x ^ 2 + c ^ 2)) x := by
    have := ((hasDerivAt_id' x).div_const c).arctan
    refine this.congr_deriv ?_
    field_simp
    ring
  have h3 : HasDerivAt (invPrimitive c)
      (((x / (x ^ 2 + c ^ 2) : ℝ) : ℂ) - I * ((c / (x ^ 2 + c ^ 2) : ℝ) : ℂ)) x :=
    h1.ofReal_comp.sub (h2.ofReal_comp.const_mul I)
  refine h3.congr_deriv ?_
  apply Complex.ext
  · rw [Complex.inv_re, Complex.normSq_apply]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, add_im, mul_im, sub_re]
    ring
  · rw [Complex.inv_im, Complex.normSq_apply]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, add_im, mul_im, sub_im]
    ring

theorem integral_inv_ofReal_add_mul_I {c : ℝ} (hc : c ≠ 0) (a b : ℝ) :
    ∫ x : ℝ in a..b, ((x : ℂ) + c * I)⁻¹ = invPrimitive c b - invPrimitive c a := by
  refine integral_eq_sub_of_hasDerivAt (fun x _ ↦ hasDerivAt_invPrimitive hc x) ?_
  refine Continuous.intervalIntegrable ?_ _ _
  exact (continuous_ofReal.add continuous_const).inv₀ (ofReal_add_mul_I_ne_zero hc)

lemma invPrimitive_rect_sum {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : a₁ < 0) (ha₂ : 0 < a₂) (hb₁ : b₁ < 0)
    (hb₂ : 0 < b₂) :
    (invPrimitive b₁ a₂ - invPrimitive b₁ a₁) - (invPrimitive b₂ a₂ - invPrimitive b₂ a₁) +
      (invPrimitive (-a₂) b₂ - invPrimitive (-a₂) b₁) -
      (invPrimitive (-a₁) b₂ - invPrimitive (-a₁) b₁) = 2 * π * I := by
  have hlog : ∀ s t : ℝ, Real.log (s ^ 2 + (-t) ^ 2) = Real.log (t ^ 2 + s ^ 2) := by
    intro s t; congr 1; ring
  have hat : ∀ s t : ℝ, Real.arctan (s / -t) = -Real.arctan (s / t) := by
    intro s t; rw [div_neg, Real.arctan_neg]
  have e1 : Real.arctan (b₂ / a₂) = π / 2 - Real.arctan (a₂ / b₂) := by
    rw [← inv_div, Real.arctan_inv_of_pos (div_pos ha₂ hb₂)]
  have e2 : Real.arctan (b₁ / a₂) = -(π / 2) - Real.arctan (a₂ / b₁) := by
    rw [← inv_div, Real.arctan_inv_of_neg (div_neg_of_pos_of_neg ha₂ hb₁)]
  have e3 : Real.arctan (b₂ / a₁) = -(π / 2) - Real.arctan (a₁ / b₂) := by
    rw [← inv_div, Real.arctan_inv_of_neg (div_neg_of_neg_of_pos ha₁ hb₂)]
  have e4 : Real.arctan (b₁ / a₁) = π / 2 - Real.arctan (a₁ / b₁) := by
    rw [← inv_div, Real.arctan_inv_of_pos (div_pos_of_neg_of_neg ha₁ hb₁)]
  simp only [invPrimitive, hlog, hat, e1, e2, e3, e4]
  push_cast
  ring

theorem rectIntegral_sub_inv {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re) (h3 : z.im < p.im)
    (h4 : p.im < w.im) : rectIntegral (fun u ↦ (u - p)⁻¹) z w = 2 * π * I := by
  have horiz : ∀ c : ℝ, c - p.im ≠ 0 → ∫ x : ℝ in z.re..w.re, ((x : ℂ) + c * I - p)⁻¹ =
      invPrimitive (c - p.im) (w.re - p.re) - invPrimitive (c - p.im) (z.re - p.re) := by
    intro c hc
    have e : ∀ x : ℝ, ((x : ℂ) + c * I - p) = ((x - p.re : ℝ) : ℂ) + ((c - p.im : ℝ) : ℂ) * I := by
      intro x; apply Complex.ext <;> simp
    simp_rw [e]
    have := intervalIntegral.integral_comp_sub_right
      (fun t : ℝ ↦ ((t : ℂ) + ((c - p.im : ℝ) : ℂ) * I)⁻¹) p.re (a := z.re) (b := w.re)
    rw [this]
    exact integral_inv_ofReal_add_mul_I hc _ _
  have vert : ∀ c : ℝ, -(c - p.re) ≠ 0 → I • ∫ y : ℝ in z.im..w.im, ((c : ℂ) + y * I - p)⁻¹ =
      invPrimitive (-(c - p.re)) (w.im - p.im) - invPrimitive (-(c - p.re)) (z.im - p.im) := by
    intro c hc
    rw [← intervalIntegral.integral_smul]
    have e : ∀ y : ℝ, I • ((c : ℂ) + y * I - p)⁻¹ =
        (((y - p.im : ℝ) : ℂ) + ((-(c - p.re) : ℝ) : ℂ) * I)⁻¹ := by
      intro y
      have hX : (c : ℂ) + y * I - p = I * (((y - p.im : ℝ) : ℂ) + ((-(c - p.re) : ℝ) : ℂ) * I) := by
        apply Complex.ext <;> simp
      rw [smul_eq_mul, hX, mul_inv, ← mul_assoc, mul_inv_cancel₀ I_ne_zero, one_mul]
    simp_rw [e]
    have := intervalIntegral.integral_comp_sub_right
      (fun t : ℝ ↦ ((t : ℂ) + ((-(c - p.re) : ℝ) : ℂ) * I)⁻¹) p.im (a := z.im) (b := w.im)
    rw [this]
    exact integral_inv_ofReal_add_mul_I hc _ _
  unfold rectIntegral
  beta_reduce
  rw [horiz _ (by linarith), horiz _ (by linarith), vert _ (by linarith), vert _ (by linarith)]
  exact invPrimitive_rect_sum (by linarith) (by linarith) (by linarith) (by linarith)

end Inverse

section Cauchy

theorem rectIntegral_eq_zero_of_differentiable_on_off_countable [CompleteSpace E] (f : ℂ → E)
    (z w : ℂ) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ s,
      DifferentiableAt ℂ f x) :
    rectIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w s hs Hc Hd

end Cauchy

section Periodic

theorem rectIntegral_eq_zero_of_periodic {g : ℂ → E} {τ : ℂ} (h1 : ∀ u, g (u + 1) = g u)
    (hτ : ∀ u, g (u + τ) = g u) (a : ℂ) : rectIntegral g a (a + 1 + τ.im * I) = 0 := by
  have hre : (a + 1 + τ.im * I).re = a.re + 1 := by simp
  have him : (a + 1 + τ.im * I).im = a.im + τ.im := by simp
  have hv : ∫ y : ℝ in a.im..a.im + τ.im, g (((a.re + 1 : ℝ) : ℂ) + y * I) =
      ∫ y : ℝ in a.im..a.im + τ.im, g ((a.re : ℂ) + y * I) := by
    congr 1
    ext y
    rw [← h1 ((a.re : ℂ) + y * I)]
    congr 1
    push_cast
    ring
  have hh : ∫ x : ℝ in a.re..a.re + 1, g ((x : ℂ) + ((a.im + τ.im : ℝ) : ℂ) * I) =
      ∫ x : ℝ in a.re..a.re + 1, g ((x : ℂ) + a.im * I) := by
    have e : ∀ x : ℝ, g ((x : ℂ) + ((a.im + τ.im : ℝ) : ℂ) * I) =
        g (((x - τ.re : ℝ) : ℂ) + a.im * I) := by
      intro x
      rw [← hτ (((x - τ.re : ℝ) : ℂ) + a.im * I)]
      congr 1
      apply Complex.ext <;> simp
    simp_rw [e]
    have := intervalIntegral.integral_comp_sub_right (fun t : ℝ ↦ g ((t : ℂ) + a.im * I)) τ.re
      (a := a.re) (b := a.re + 1)
    rw [this]
    have hper : Function.Periodic (fun t : ℝ ↦ g ((t : ℂ) + a.im * I)) 1 := by
      intro t
      beta_reduce
      rw [← h1 ((t : ℂ) + a.im * I)]
      congr 1
      push_cast
      ring
    rw [show a.re + 1 - τ.re = a.re - τ.re + 1 by ring]
    exact hper.intervalIntegral_add_eq (a.re - τ.re) a.re
  unfold rectIntegral
  rw [hre, him, hv, hh]
  abel

end Periodic

end Elliptic
end GroundTheory.Global
