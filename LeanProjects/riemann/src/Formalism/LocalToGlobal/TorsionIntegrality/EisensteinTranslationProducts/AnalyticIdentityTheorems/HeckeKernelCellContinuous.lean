import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HkRowIntegral

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace Hk2

lemma rpow_bd {κ x t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hx : κ ≤ x) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    x ^ (-t) ≤ (κ ^ 2)⁻¹ := by
  calc x ^ (-t) ≤ κ ^ (-t) := Real.rpow_le_rpow_of_nonpos hκ hx (by linarith)
    _ ≤ κ ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_ge hκ hκ1 (by linarith)
    _ = (κ ^ 2)⁻¹ := by rw [Real.rpow_neg hκ.le, Real.rpow_two]

lemma rpow_diff {κ ρ a b t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hρ : κ ≤ ρ) (ha : ρ ≤ a) (hb : ρ ≤ b)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |a ^ (-t) - b ^ (-t)| ≤ 2 * (κ ^ 2)⁻¹ * ρ⁻¹ * |a - b| := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hκ hρ
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
    (f := fun x : ℝ => x ^ (-t)) (f' := fun x : ℝ => (-t) * x ^ (-t - 1)) (s := Set.Ici ρ)
    (C := 2 * (κ ^ 2)⁻¹ * ρ⁻¹) (x := b) (y := a)
    (fun x hx => (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (lt_of_lt_of_le hρ0 hx)))).hasDerivWithinAt)
    (fun x hx => by
      have hx' : ρ ≤ x := hx
      have hx0 : 0 < x := lt_of_lt_of_le hρ0 hx'
      rw [Real.rpow_sub hx0, Real.rpow_one, norm_mul, norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_neg, abs_of_nonneg ht0, abs_of_pos hx0,
        abs_of_nonneg (Real.rpow_nonneg hx0.le _), div_eq_mul_inv, ← mul_assoc]
      have h1 := rpow_bd hκ hκ1 (hρ.trans hx') ht0 ht2
      have h2 : x⁻¹ ≤ ρ⁻¹ := inv_anti₀ hρ0 hx'
      have h3 : 0 ≤ x ^ (-t) := Real.rpow_nonneg hx0.le _
      gcongr)
    (convex_Ici ρ) hb ha
  simpa [Real.norm_eq_abs] using key

lemma inv_sq_diff {ρ : ℝ} {w w' : ℂ} (hρ : 0 < ρ) (hw : ρ ≤ ‖w‖) (hw' : ρ ≤ ‖w'‖) :
    ‖(w ^ 2)⁻¹ - (w' ^ 2)⁻¹‖ ≤ 2 * (ρ ^ 3)⁻¹ * ‖w - w'‖ := by
  have h0 : w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hρ hw)
  have h0' : w' ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hρ hw')
  have e : (w ^ 2)⁻¹ - (w' ^ 2)⁻¹ = (w' - w) * (w⁻¹ * (w' ^ 2)⁻¹ + (w ^ 2)⁻¹ * w'⁻¹) := by
    field_simp
    ring
  have i1 : ‖w‖⁻¹ ≤ ρ⁻¹ := inv_anti₀ hρ hw
  have i2 : ‖w'‖⁻¹ ≤ ρ⁻¹ := inv_anti₀ hρ hw'
  have p1 : 0 ≤ ‖w‖⁻¹ := by positivity
  have p2 : 0 ≤ ‖w'‖⁻¹ := by positivity
  have b1 : ‖w⁻¹ * (w' ^ 2)⁻¹‖ ≤ (ρ ^ 3)⁻¹ := by
    rw [norm_mul, norm_inv, norm_inv, norm_pow, ← inv_pow, ← inv_pow]
    calc ‖w‖⁻¹ * ‖w'‖⁻¹ ^ 2 ≤ ρ⁻¹ * ρ⁻¹ ^ 2 := by gcongr
      _ = ρ⁻¹ ^ 3 := by ring
  have b2 : ‖(w ^ 2)⁻¹ * w'⁻¹‖ ≤ (ρ ^ 3)⁻¹ := by
    rw [norm_mul, norm_inv, norm_inv, norm_pow, ← inv_pow, ← inv_pow]
    calc ‖w‖⁻¹ ^ 2 * ‖w'‖⁻¹ ≤ ρ⁻¹ ^ 2 * ρ⁻¹ := by gcongr
      _ = ρ⁻¹ ^ 3 := by ring
  rw [e, norm_mul, norm_sub_rev w' w, mul_comm]
  gcongr
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (ρ ^ 3)⁻¹ + (ρ ^ 3)⁻¹ := add_le_add b1 b2
    _ = 2 * (ρ ^ 3)⁻¹ := by ring

lemma hk_diff {κ ρ s : ℝ} {w w' : ℂ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hρ : κ ≤ ρ) (hw : ρ ≤ ‖w‖)
    (hw' : ρ ≤ ‖w'‖) (hd : ‖w - w'‖ ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖hk s w - hk s w'‖ ≤ 4 * (κ ^ 2)⁻¹ * (ρ ^ 3)⁻¹ := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hκ hρ
  have e : hk s w - hk s w' = ((w ^ 2)⁻¹ - (w' ^ 2)⁻¹) * ((‖w‖ ^ (-(2 * s)) : ℝ) : ℂ)
      + (w' ^ 2)⁻¹ * ((‖w‖ ^ (-(2 * s)) - ‖w'‖ ^ (-(2 * s)) : ℝ) : ℂ) := by
    unfold hk
    push_cast
    ring
  have a1 : ‖(w ^ 2)⁻¹ - (w' ^ 2)⁻¹‖ ≤ 2 * (ρ ^ 3)⁻¹ := by
    refine (inv_sq_diff hρ0 hw hw').trans ?_
    have : 0 ≤ 2 * (ρ ^ 3)⁻¹ := by positivity
    nlinarith
  have a2 : ‖((‖w‖ ^ (-(2 * s)) : ℝ) : ℂ)‖ ≤ (κ ^ 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact rpow_bd hκ hκ1 (hρ.trans hw) (by linarith) (by linarith)
  have a3 : ‖(w' ^ 2)⁻¹‖ ≤ (ρ ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow]
    exact inv_anti₀ (by positivity) (by gcongr)
  have a4 : ‖((‖w‖ ^ (-(2 * s)) - ‖w'‖ ^ (-(2 * s)) : ℝ) : ℂ)‖ ≤ 2 * (κ ^ 2)⁻¹ * ρ⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (rpow_diff hκ hκ1 hρ hw hw' (by linarith) (by linarith)).trans ?_
    have h1 : |‖w‖ - ‖w'‖| ≤ 1 := (abs_norm_sub_norm_le w w').trans hd
    have : 0 ≤ 2 * (κ ^ 2)⁻¹ * ρ⁻¹ := by positivity
    nlinarith
  rw [e]
  calc _ ≤ ‖((w ^ 2)⁻¹ - (w' ^ 2)⁻¹) * ((‖w‖ ^ (-(2 * s)) : ℝ) : ℂ)‖
        + ‖(w' ^ 2)⁻¹ * ((‖w‖ ^ (-(2 * s)) - ‖w'‖ ^ (-(2 * s)) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 * (ρ ^ 3)⁻¹ * (κ ^ 2)⁻¹ + (ρ ^ 2)⁻¹ * (2 * (κ ^ 2)⁻¹ * ρ⁻¹) := by
        rw [norm_mul, norm_mul]
        gcongr
    _ = 4 * (κ ^ 2)⁻¹ * (ρ ^ 3)⁻¹ := by
        field_simp
        ring

def kap (τ : ℂ) : ℝ := |τ.im| / (|τ.im| + 2 + |τ.re|)

lemma kap_pos {τ : ℂ} (hτ : τ.im ≠ 0) : 0 < kap τ := by
  have : 0 < |τ.im| := abs_pos.mpr hτ
  unfold kap
  positivity

lemma kap_le_one (τ : ℂ) : kap τ ≤ 1 := by
  unfold kap
  have h1 : 0 ≤ |τ.im| := abs_nonneg _
  have h2 : 0 ≤ |τ.re| := abs_nonneg _
  rw [div_le_one (by linarith)]
  linarith

lemma lower {τ : ℂ} (m n : ℤ) (hn : n ≠ 0) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    kap τ * (|(m : ℝ)| + |(n : ℝ)|) ≤ ‖(m : ℂ) + (x : ℂ) + (n : ℂ) * τ‖ := by
  set W := ‖(m : ℂ) + (x : ℂ) + (n : ℂ) * τ‖ with hW
  have hY : 0 ≤ |τ.im| := abs_nonneg _
  have hA : 0 ≤ |τ.re| := abs_nonneg _
  have hN : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    exact_mod_cast this
  have h1 : |(n : ℝ)| * |τ.im| ≤ W := by
    have := Complex.abs_im_le_norm ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ)
    simpa [abs_mul] using this
  have h2 : |(m : ℝ)| ≤ W + |(n : ℝ)| + |(n : ℝ)| * |τ.re| := by
    have h := Complex.abs_re_le_norm ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ)
    have e : ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ).re = (m : ℝ) + x + (n : ℝ) * τ.re := by simp
    rw [e] at h
    have e2 : (m : ℝ) = ((m : ℝ) + x + (n : ℝ) * τ.re) - x - (n : ℝ) * τ.re := by ring
    calc |(m : ℝ)| = |((m : ℝ) + x + (n : ℝ) * τ.re) - x - (n : ℝ) * τ.re| := by rw [← e2]
      _ ≤ |((m : ℝ) + x + (n : ℝ) * τ.re) - x| + |(n : ℝ) * τ.re| := abs_sub _ _
      _ ≤ |(m : ℝ) + x + (n : ℝ) * τ.re| + |x| + |(n : ℝ) * τ.re| := by
          gcongr
          exact abs_sub _ _
      _ ≤ W + |(n : ℝ)| + |(n : ℝ)| * |τ.re| := by
          rw [abs_mul, abs_of_nonneg hx0]
          gcongr
          linarith
  unfold kap
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  have k1 := mul_le_mul_of_nonneg_left h2 hY
  have k2 := mul_le_mul_of_nonneg_right h1 hA
  nlinarith

lemma summ : Summable (fun p : ℤ × ℤ => ((|(p.1 : ℝ)| + |(p.2 : ℝ)|) ^ 3)⁻¹) := by
  have h := EisensteinSeries.summable_one_div_norm_rpow (k := 3) (by norm_num)
  rw [← (finTwoArrowEquiv ℤ).symm.summable_iff] at h
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) h
  simp only [Function.comp, finTwoArrowEquiv_symm_apply]
  have hN : ‖![p.1, p.2]‖ = max |(p.1 : ℝ)| |(p.2 : ℝ)| := by
    rw [EisensteinSeries.norm_eq_max_natAbs]
    simp [Nat.cast_natAbs]
  rw [hN]
  have q1 : 0 ≤ |(p.1 : ℝ)| := abs_nonneg _
  have q2 : 0 ≤ |(p.2 : ℝ)| := abs_nonneg _
  rcases eq_or_lt_of_le (le_max_of_le_left q1 : 0 ≤ max |(p.1 : ℝ)| |(p.2 : ℝ)|) with h0 | h0
  · have z1 : |(p.1 : ℝ)| = 0 := le_antisymm (h0 ▸ le_max_left _ _) q1
    have z2 : |(p.2 : ℝ)| = 0 := le_antisymm (h0 ▸ le_max_right _ _) q2
    rw [z1, z2]
    simp
  · rw [Real.rpow_neg h0.le]
    have : (max |(p.1 : ℝ)| |(p.2 : ℝ)|) ^ (3 : ℝ) = (max |(p.1 : ℝ)| |(p.2 : ℝ)|) ^ 3 := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [this]
    apply inv_anti₀ (by positivity)
    gcongr
    exact max_le (by linarith) (by linarith)

lemma pt_ne_zero {τ : ℂ} (hτ : τ.im ≠ 0) {n : ℤ} (hn : n ≠ 0) (m : ℤ) (x : ℝ) :
    (m : ℂ) + (x : ℂ) + (n : ℂ) * τ ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  rcases this with h | h
  · exact hn h
  · exact hτ h

lemma hk_cont {τ : ℂ} (hτ : τ.im ≠ 0) {n : ℤ} (hn : n ≠ 0) (m : ℤ) :
    Continuous (Function.uncurry fun (s x : ℝ) => hk s ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ)) := by
  unfold hk Function.uncurry
  have c : Continuous fun q : ℝ × ℝ => (m : ℂ) + ((q.2 : ℝ) : ℂ) + (n : ℂ) * τ := by fun_prop
  refine Continuous.mul ?_ ?_
  · exact (c.pow 2).inv₀ (fun q => pow_ne_zero 2 (pt_ne_zero hτ hn m q.2))
  · refine Complex.continuous_ofReal.comp ?_
    refine Continuous.rpow c.norm (by fun_prop) (fun q => Or.inl ?_)
    exact norm_ne_zero_iff.mpr (pt_ne_zero hτ hn m q.2)

lemma cell_cont {τ : ℂ} (hτ : τ.im ≠ 0) {p : ℤ × ℤ} (hp : p.2 ≠ 0) :
    Continuous fun s : ℝ => hkCell τ s p := by
  unfold hkCell
  refine Continuous.sub ?_ ?_
  · have h := (hk_cont hτ hp p.1).comp (Continuous.prodMk continuous_id (continuous_const (y := (0 : ℝ))))
    simpa [Function.uncurry, Function.comp_def] using h
  · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hk_cont hτ hp p.1) 0 1

lemma cell_bound {τ : ℂ} (hτ : τ.im ≠ 0) {p : ℤ × ℤ} (hp : p.2 ≠ 0) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    ‖hkCell τ s p‖ ≤ 4 * (kap τ ^ 2)⁻¹ * ((kap τ * (|(p.1 : ℝ)| + |(p.2 : ℝ)|)) ^ 3)⁻¹ := by
  have hκ := kap_pos hτ
  have hκ1 := kap_le_one τ
  have hN : (1 : ℝ) ≤ |(p.2 : ℝ)| := by
    have : (1 : ℤ) ≤ |p.2| := Int.one_le_abs hp
    exact_mod_cast this
  have hρ : kap τ ≤ kap τ * (|(p.1 : ℝ)| + |(p.2 : ℝ)|) := by
    have : 0 ≤ |(p.1 : ℝ)| := abs_nonneg _
    nlinarith
  have cx : Continuous fun x : ℝ => hk s ((p.1 : ℂ) + (x : ℂ) + (p.2 : ℂ) * τ) := by
    have h := (hk_cont hτ hp p.1).comp (Continuous.prodMk (continuous_const (y := s)) continuous_id)
    simpa [Function.uncurry, Function.comp_def] using h
  have e : hkCell τ s p = ∫ x in (0 : ℝ)..1, (hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ)
      - hk s ((p.1 : ℂ) + (x : ℂ) + (p.2 : ℂ) * τ)) := by
    rw [intervalIntegral.integral_sub (by simp) (cx.intervalIntegrable 0 1)]
    simp [hkCell]
  rw [e]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := 4 * (kap τ ^ 2)⁻¹ * ((kap τ * (|(p.1 : ℝ)| + |(p.2 : ℝ)|)) ^ 3)⁻¹)
    (f := fun x : ℝ => hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ) - hk s ((p.1 : ℂ) + (x : ℂ) + (p.2 : ℂ) * τ))
    (fun x hx => by
      rw [Set.uIoc_of_le zero_le_one] at hx
      have l0 := lower (τ := τ) p.1 p.2 hp (le_refl (0 : ℝ)) zero_le_one
      have lx := lower (τ := τ) p.1 p.2 hp hx.1.le hx.2
      simp only [Complex.ofReal_zero, add_zero] at l0
      refine hk_diff hκ hκ1 hρ l0 lx ?_ hs0 hs1
      have : (p.1 : ℂ) + (p.2 : ℂ) * τ - ((p.1 : ℂ) + (x : ℂ) + (p.2 : ℂ) * τ) = -(x : ℂ) := by ring
      rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
      exact hx.2)
  simpa using this

end Hk2

theorem hecke_kernel_cell_bound : HkCellBound := by
  intro τ hτ
  refine ⟨fun p => 4 * (Hk2.kap τ ^ 2)⁻¹ * ((Hk2.kap τ * (|(p.1 : ℝ)| + |(p.2 : ℝ)|)) ^ 3)⁻¹, ?_,
    fun s p hs0 hs1 hp => Hk2.cell_bound hτ hp hs0 hs1⟩
  have h := Hk2.summ.mul_left (4 * (Hk2.kap τ ^ 2)⁻¹ * (Hk2.kap τ ^ 3)⁻¹)
  refine h.congr (fun p => ?_)
  rw [mul_pow, mul_inv]
  ring

theorem hecke_kernel_cell_continuous : HkCellCont := by
  intro τ p hτ hp
  exact ((Hk2.cell_cont hτ hp).tendsto 0).mono_left nhdsWithin_le_nhds

end Formalism.L2.Th1.F
