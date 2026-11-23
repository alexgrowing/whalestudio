import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.SepNodeQuad

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private lemma pow_le_exp_eventually (d : ℕ → ℕ) (hd : Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0))
    (L : ℝ) (hL : 0 < L) : ∀ᶠ j : ℕ in atTop, L ^ (d j + 1) ≤ Real.exp j := by
  have h1 : Tendsto (fun j : ℕ => Real.log L * ((d j : ℝ) / j + 1 / j)) atTop
      (𝓝 (Real.log L * (0 + 0))) :=
    (hd.add tendsto_one_div_atTop_nhds_zero_nat).const_mul _
  have h2 := h1.eventually (gt_mem_nhds (show Real.log L * (0 + 0) < 1 by simp))
  filter_upwards [h2, eventually_gt_atTop 0] with j hj hj0
  have hjp : (0 : ℝ) < j := by exact_mod_cast hj0
  have h3 : Real.log L * ((d j : ℝ) + 1) ≤ j := by
    have : Real.log L * ((d j : ℝ) / j + 1 / j) = Real.log L * ((d j : ℝ) + 1) / j := by ring
    rw [this, div_lt_one hjp] at hj
    exact hj.le
  calc L ^ (d j + 1) = Real.exp (Real.log L * ((d j : ℝ) + 1)) := by
        rw [← Real.rpow_def_of_pos hL]
        rw [← Real.rpow_natCast]; push_cast; rfl
    _ ≤ _ := Real.exp_le_exp.2 h3

private lemma err_bound2 (p : ℕ) (hp : 0 < p) (c₁ cq a₀ : ℝ) (h0 : 0 < a₀) (h1 : a₀ ≤ 1)
    (A η : ℝ) (hA : A = |c₁ + cq + 1| + 1) (hηp : 0 < η) (hη : η ≤ a₀ * Real.exp (-(p * A))) (j : ℕ) (F : ℝ)
    (hF : Real.exp ((c₁ + cq + 2 + Real.log (4 / a₀)) * j) ≤ F) :
    Real.exp ((cq + 1) * j) * (η / a₀) ^ (j / p) *
      (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / F) +
        (4 / η) ^ (j / p) * Real.exp (-(cq + 2 + Real.log (4 / a₀)) * j)) ≤
      (Real.exp (p * A) + 2) * Real.exp (-j) := by
  have hFp : 0 < F := (Real.exp_pos _).trans_le hF
  set m := j / p with hm
  set g := Real.log (4 / a₀) with hg
  have hq : (η / a₀) ^ m * (4 / η) ^ m = (4 / a₀) ^ m := by
    rw [← mul_pow]; congr 1; field_simp
  have h4 : (4 / a₀) ^ m ≤ Real.exp (g * j) := by
    have : (1 : ℝ) ≤ 4 / a₀ := by rw [le_div_iff₀ h0]; linarith
    calc (4 / a₀) ^ m ≤ (4 / a₀) ^ j := pow_le_pow_right₀ this (Nat.div_le_self _ _)
      _ = Real.exp (g * j) := by
        rw [mul_comm, Real.exp_nat_mul, hg, Real.exp_log (by positivity)]
  have h5 : (η / a₀) ^ m ≤ Real.exp (-(m * p * A)) := by
    have : η / a₀ ≤ Real.exp (-(p * A)) := by rw [div_le_iff₀ h0, mul_comm]; exact hη
    calc _ ≤ Real.exp (-(p * A)) ^ m := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hmp : (j : ℝ) ≤ m * p + p := by
    have := Nat.lt_div_mul_add (a := j) hp
    rw [← hm] at this
    exact_mod_cast this.le
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hA1 : c₁ + cq + 2 ≤ A := by have := le_abs_self (c₁ + cq + 1); linarith
  have t1 : Real.exp ((cq + 1) * j) * (η / a₀) ^ m * Real.exp (c₁ * j) ≤
      Real.exp (p * A) * Real.exp (-j) := by
    refine le_trans (b := Real.exp ((cq + 1) * j) * Real.exp (-(m * p * A)) * Real.exp (c₁ * j))
      (by gcongr) ?_
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_right hmp hA0, mul_le_mul_of_nonneg_right hA1 hj]
  have t2 : Real.exp ((cq + 1) * j) * Real.exp (c₁ * j) * (4 / a₀) ^ m / F ≤ Real.exp (-j) := by
    rw [div_le_iff₀ hFp]
    calc _ ≤ Real.exp ((cq + 1) * j) * Real.exp (c₁ * j) * Real.exp (g * j) := by gcongr
      _ = Real.exp (-j) * Real.exp ((c₁ + cq + 2 + g) * j) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := by gcongr
  have t3 : Real.exp ((cq + 1) * j) * (4 / a₀) ^ m * Real.exp (-(cq + 2 + g) * j) ≤
      Real.exp (-j) := by
    calc _ ≤ Real.exp ((cq + 1) * j) * Real.exp (g * j) * Real.exp (-(cq + 2 + g) * j) := by gcongr
      _ = Real.exp (-j) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [← hq] at t2 t3
  calc _ = Real.exp ((cq + 1) * j) * (η / a₀) ^ m * Real.exp (c₁ * j) +
        Real.exp ((cq + 1) * j) * Real.exp (c₁ * j) * ((η / a₀) ^ m * (4 / η) ^ m) / F +
        Real.exp ((cq + 1) * j) * ((η / a₀) ^ m * (4 / η) ^ m) * Real.exp (-(cq + 2 + g) * j) := by
        ring
    _ ≤ _ := by linarith

private lemma solve_bound2 (x a z η a₀ cq K₁ K E : ℝ) (d m j : ℕ) (hx : 0 ≤ x) (hη : 0 < η)
    (hηa : η < a₀) (h1 : a₀ ≤ 1) (ha : a₀ ≤ a) (hz : Real.exp (-cq) ≤ z) (hE : 0 ≤ E)
    (hL : ((|K₁| + 1) * |K| / a₀ + 1) ^ (d + 1) ≤ Real.exp j)
    (h : x * a ^ d * (2 * a / η - 1) ^ m * z ^ j ≤ K₁ * (K ^ (d + 1) * E)) :
    x ≤ Real.exp ((cq + 1) * j) * (η / a₀) ^ m * E := by
  have h0 : 0 < a₀ := hη.trans hηa
  have hb : a₀ / η ≤ 2 * a / η - 1 := by
    rw [div_sub_one hη.ne', div_le_div_iff_of_pos_right hη]; linarith
  have hb0 : 0 < a₀ / η := by positivity
  have hl : x * a₀ ^ (d + 1) * (a₀ / η) ^ m * Real.exp (-cq) ^ j ≤
      x * a ^ d * (2 * a / η - 1) ^ m * z ^ j := by
    have : a₀ ^ (d + 1) ≤ a ^ d :=
      (pow_le_pow_of_le_one h0.le h1 (Nat.le_succ d)).trans (pow_le_pow_left₀ h0.le ha d)
    have h2 : 0 ≤ a := by linarith
    have h3 : 0 ≤ 2 * a / η - 1 := by linarith
    gcongr
  have hr : K₁ * (K ^ (d + 1) * E) ≤ a₀ ^ (d + 1) * Real.exp j * E := by
    have e1 : |K₁| ≤ (|K₁| + 1) ^ (d + 1) :=
      (by linarith : |K₁| ≤ |K₁| + 1).trans
        (le_self_pow₀ (by linarith [abs_nonneg K₁]) (Nat.succ_ne_zero d))
    calc K₁ * (K ^ (d + 1) * E) ≤ |K₁ * (K ^ (d + 1) * E)| := le_abs_self _
      _ = |K₁| * |K| ^ (d + 1) * E := by
        rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hE, mul_assoc]
      _ ≤ (|K₁| + 1) ^ (d + 1) * |K| ^ (d + 1) * E := by gcongr
      _ = a₀ ^ (d + 1) * ((|K₁| + 1) * |K| / a₀) ^ (d + 1) * E := by
        rw [← mul_pow, ← mul_pow]; congr 2; field_simp
      _ ≤ a₀ ^ (d + 1) * ((|K₁| + 1) * |K| / a₀ + 1) ^ (d + 1) * E := by
        gcongr; linarith
      _ ≤ _ := by gcongr
  have h6 := (hl.trans h).trans hr
  have hpos : 0 < a₀ ^ (d + 1) * (a₀ / η) ^ m * Real.exp (-cq) ^ j := by positivity
  have e2 : (η / a₀) ^ m * (a₀ / η) ^ m = 1 := by
    rw [← mul_pow]
    have : η / a₀ * (a₀ / η) = 1 := by field_simp
    rw [this, one_pow]
  have e3 : Real.exp ((cq + 1) * j) * Real.exp (-cq) ^ j = Real.exp j := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  refine le_of_mul_le_mul_right ?_ hpos
  calc _ = x * a₀ ^ (d + 1) * (a₀ / η) ^ m * Real.exp (-cq) ^ j := by ring
    _ ≤ a₀ ^ (d + 1) * Real.exp j * E := h6
    _ = a₀ ^ (d + 1) * (Real.exp ((cq + 1) * j) * Real.exp (-cq) ^ j) *
        ((η / a₀) ^ m * (a₀ / η) ^ m) * E := by rw [e2, e3, mul_one]
    _ = _ := by ring

theorem UpperTheory.ConvolutionTheory.FX.exponents2 :
    ∀ (d : ℕ → ℕ), Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0) →
    (∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) →
    ∀ (p : ℕ), 0 < p → ∀ (c₁ cq a₀ : ℝ), 0 < a₀ → a₀ ≤ 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < a₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ N : ℝ,
    ∀ (I : Type) [Fintype I] (a : I → ℝ) (ζ : I → ℂ), (∀ i, η < a i) → (∀ i, ζ i ≠ 0) →
    Function.Injective (fun i => (a i, ζ i)) → ∀ (c : ℕ → I → ℂ) (c' : I → ℂ),
    (∀ i, Tendsto (fun j => c j i) atTop (𝓝 (c' i))) →
    (∀ s₀ : ℕ, ∃ K : ℝ, ∀ᶠ j : ℕ in atTop, ∀ s ≤ s₀, ∀ s' ≤ s₀,
    ‖∑ i, c j i * (a i : ℂ) ^ d j * (cheb η (j / p + s) (a i) : ℂ) * ζ i ^ (j + s')‖ ≤
    K ^ (d j + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) →
    ∀ i, a₀ ≤ a i → Real.exp (-cq) ≤ ‖ζ i‖ → c' i = 0 := by
  intro d hd hfac p hp c₁ cq a₀ h0 h1
  obtain ⟨A, hA⟩ : ∃ A, A = |c₁ + cq + 1| + 1 := ⟨_, rfl⟩
  have hη₀a : a₀ * Real.exp (-(p * A)) < a₀ := by
    have hA0 : 0 < A := by rw [hA]; positivity
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have : Real.exp (-(p * A)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [mul_pos hp' hA0])
    nlinarith
  refine ⟨a₀ * Real.exp (-(p * A)), by positivity, hη₀a, ?_⟩
  intro η hηp hη
  have hηa : η < a₀ := hη.trans_lt hη₀a
  refine ⟨cq + 2 + Real.log (4 / a₀), ?_⟩
  intro I _ a ζ ha hζ0 hinj c c' hc hbd i hi hζ
  obtain ⟨s₀, K₁, hsep⟩ := UpperTheory.ConvolutionTheory.FX.separate0 η hηp I a ζ ha hζ0 hinj
  obtain ⟨K, hK⟩ := hbd s₀
  have hev : ∀ᶠ j : ℕ in atTop, ‖c j i‖ ≤ (Real.exp (p * A) + 2) * Real.exp (-j) := by
    filter_upwards [hK, hfac (c₁ + cq + 2 + Real.log (4 / a₀)),
      pow_le_exp_eventually d hd ((|K₁| + 1) * |K| / a₀ + 1) (by positivity)] with j hj hF hL
    have h := hsep (j / p) j (fun i => c j i * (a i : ℂ) ^ d j) _ hj i
    have hai : 0 ≤ a i := by linarith
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hai] at h
    exact (solve_bound2 _ _ _ η a₀ cq K₁ K _ _ _ _ (norm_nonneg _) hηp hηa h1 hi hζ
      (by positivity) hL h).trans (err_bound2 p hp c₁ cq a₀ h0 h1 A η hA hηp hη j _ hF)
  have hlim : Tendsto (fun j : ℕ => (Real.exp (p * A) + 2) * Real.exp (-j)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul
      (Real.exp (p * A) + 2)
    simpa using this
  exact tendsto_nhds_unique (hc i) (squeeze_zero_norm' hev hlim)
