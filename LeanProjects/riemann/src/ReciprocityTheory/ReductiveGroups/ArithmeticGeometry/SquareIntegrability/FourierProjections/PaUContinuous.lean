import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.HfEqInner

namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

theorem lat_countable {κ : Type} [Fintype κ] (b : Module.Basis κ ℝ (EuclideanSpace ℂ ι)) :
    Countable (lat b) := by
  let f : (κ → ℤ) → lat b := fun c => ⟨∑ i, c i • b i,
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
    exact ⟨c, Subtype.ext hc⟩
  exact hf.countable

theorem Hf_continuous (a : EuclideanSpace ℂ ι) : Continuous fun v : EuclideanSpace ℂ ι => Hf v a := by
  simp_rw [Hf_eq_inner]
  exact continuous_const.inner continuous_id

theorem paU_continuous {q c : ℕ} (a : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ paPoly c) : Continuous (paU q a F) := by
  unfold paU
  exact (Complex.continuous_exp.comp ((continuous_const.mul (Hf_continuous a)).sub continuous_const)).mul
    ((paPoly_continuous hF).comp (continuous_id.sub continuous_const))

theorem paU_norm_mul (q : ℕ) (a v : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) :
    ‖paU q a F v‖ * paW q v = ‖F (v - a)‖ * (Real.exp (-(q * Real.pi) * ‖v - (1 / 2 : ℂ) • a‖ ^ 2) *
      Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) := by
  have hre : (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2 : ℂ).re =
      q * Real.pi * RCLike.re (inner ℂ a v) - q * Real.pi * ‖a‖ ^ 2 / 2 := by
    rw [Hf_eq_inner, Hf_eq_inner, inner_self_eq_norm_sq_to_K]
    simp [Complex.mul_re]
    left
    rw [← Complex.ofReal_pow]
    exact Complex.ofReal_re _
  have hsq : ‖v - (1 / 2 : ℂ) • a‖ ^ 2 = ‖v‖ ^ 2 - RCLike.re (inner ℂ a v) + ‖a‖ ^ 2 / 4 := by
    rw [@norm_sub_sq ℂ, inner_smul_right, norm_smul]
    simp
    rw [← inner_conj_symm v a, Complex.conj_re]
    ring
  unfold paU paW
  rw [norm_mul, Complex.norm_exp, hre, hsq, mul_comm (Real.exp _) ‖F (v - a)‖, mul_assoc,
    ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

def paK (q c : ℕ) (u : EuclideanSpace ℂ ι) : ℝ := (1 + ‖u‖) ^ (2 * c) * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2)

theorem paK_integrable {q : ℕ} (hq : 1 ≤ q) (c : ℕ) : Integrable (paK (ι := ι) q c) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  refine pa_integrable_of_le (f := paK q c) ?_ (2 * c) (b := q * Real.pi) (C := 1) (by positivity)
    zero_le_one fun u => ?_
  · unfold paK
    fun_prop
  · rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by unfold paK; positivity)]
    rfl

theorem paU_int {q c : ℕ} (hq : 1 ≤ q) {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (hG : G ∈ paPoly c) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : EuclideanSpace ℂ ι,
      Integrable (fun v => ‖paU q a F v‖ * ‖G v‖ * paW q v) ∧
      ∫ v, ‖paU q a F v‖ * ‖G v‖ * paW q v ≤
        C * ((1 + ‖a‖) ^ (2 * c) * Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) := by
  obtain ⟨C1, hC1, hF1⟩ := paPoly_growth hF
  obtain ⟨C2, hC2, hG1⟩ := paPoly_growth hG
  have hK := paK_integrable (ι := ι) hq c
  have hK0 : 0 ≤ ∫ u, paK (ι := ι) q c u :=
    integral_nonneg fun u => by unfold paK; positivity
  refine ⟨C1 * C2 * ∫ u, paK q c u, by positivity, fun a => ?_⟩
  set A : ℝ := (1 + ‖a‖) ^ (2 * c) * Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4) with hA
  have hbound : ∀ v, ‖paU q a F v‖ * ‖G v‖ * paW q v ≤
      C1 * C2 * A * paK q c (v - (1 / 2 : ℂ) • a) := by
    intro v
    have e := paU_norm_mul q a v F
    rw [mul_right_comm, e]
    set u := v - (1 / 2 : ℂ) • a with hu
    have hva : v - a = u - (1 / 2 : ℂ) • a := by
      rw [hu, sub_sub, ← add_smul]
      norm_num
    have hv : v = u + (1 / 2 : ℂ) • a := by rw [hu, sub_add_cancel]
    have hhalf : ‖(1 / 2 : ℂ) • a‖ = ‖a‖ / 2 := by
      rw [norm_smul]
      norm_num
      ring
    have hu0 := norm_nonneg u
    have ha0 := norm_nonneg a
    have h1 : 1 + ‖v - a‖ ≤ (1 + ‖u‖) * (1 + ‖a‖) := by
      have := norm_sub_le u ((1 / 2 : ℂ) • a)
      rw [hva]
      nlinarith
    have h2 : 1 + ‖v‖ ≤ (1 + ‖u‖) * (1 + ‖a‖) := by
      have := norm_add_le u ((1 / 2 : ℂ) • a)
      rw [hv]
      nlinarith
    have hE1 := Real.exp_pos (-(q * Real.pi) * ‖u‖ ^ 2)
    have hE2 := Real.exp_pos (-(q * Real.pi) * ‖a‖ ^ 2 / 4)
    calc ‖F (v - a)‖ * (Real.exp (-(q * Real.pi) * ‖u‖ ^ 2) *
          Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) * ‖G v‖
        ≤ (C1 * (1 + ‖v - a‖) ^ c) * (Real.exp (-(q * Real.pi) * ‖u‖ ^ 2) *
          Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) * (C2 * (1 + ‖v‖) ^ c) := by
          gcongr
          · exact hF1 _
          · exact hG1 _
      _ = C1 * C2 * ((1 + ‖v - a‖) ^ c * (1 + ‖v‖) ^ c) *
          (Real.exp (-(q * Real.pi) * ‖u‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) := by ring
      _ ≤ C1 * C2 * (((1 + ‖u‖) * (1 + ‖a‖)) ^ c * ((1 + ‖u‖) * (1 + ‖a‖)) ^ c) *
          (Real.exp (-(q * Real.pi) * ‖u‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) := by
          gcongr
      _ = C1 * C2 * A * paK q c u := by
          rw [hA]
          unfold paK
          rw [← pow_add, ← two_mul, mul_pow]
          ring
  have hcont : Continuous fun v => ‖paU q a F v‖ * ‖G v‖ * paW q v :=
    ((paU_continuous a hF).norm.mul (paPoly_continuous hG).norm).mul (paW_continuous q)
  have hKa : Integrable fun v => C1 * C2 * A * paK q c (v - (1 / 2 : ℂ) • a) :=
    (hK.comp_sub_right _).const_mul _
  have hint : Integrable fun v => ‖paU q a F v‖ * ‖G v‖ * paW q v :=
    hKa.mono' hcont.aestronglyMeasurable (ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (paW_pos q v).le)]
      exact hbound v)
  refine ⟨hint, ?_⟩
  calc ∫ v, ‖paU q a F v‖ * ‖G v‖ * paW q v
      ≤ ∫ v, C1 * C2 * A * paK q c (v - (1 / 2 : ℂ) • a) := integral_mono hint hKa hbound
    _ = C1 * C2 * A * ∫ u, paK q c u := by
        rw [integral_const_mul, integral_sub_right_eq_self]
    _ = C1 * C2 * (∫ u, paK q c u) * A := by ring

theorem lat_summable (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (Y : GT ι) {q c : ℕ} {R0 : ℝ}
    (hq : 1 ≤ q) (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (hR : 16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2) :
    Summable (fun γ : lat Y.b => (1 + ‖(γ : EuclideanSpace ℂ ι)‖) ^ (2 * c) *
      Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 4)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hb : (0 : ℝ) < q * Real.pi / 4 := by positivity
  obtain hT := (paTail hP hA Y hq hR0 hlat hR).1
  set K : ℝ := 2 ^ (2 * c) * (2 + (2 * c).factorial * (2 / (q * Real.pi / 4)) ^ (2 * c)) with hK
  have hind : Summable fun γ : lat Y.b => if (γ : EuclideanSpace ℂ ι) = 0 then (1 : ℝ) else 0 := by
    simpa using (hasSum_ite_eq (0 : lat Y.b) (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le (fun γ => by positivity) (fun γ => ?_) ((hT.mul_left K).add hind)
  have hle := pa_pow_gauss_le (2 * c) hb (norm_nonneg (γ : EuclideanSpace ℂ ι))
  have he : Real.exp (-(q * Real.pi / 4 / 2) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) ≤
      Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16) := by
    apply Real.exp_le_exp.2
    have : 0 ≤ q * Real.pi * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 := by positivity
    linarith
  have hform : -(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 4 =
      -(q * Real.pi / 4) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 := by ring
  by_cases h0 : (γ : EuclideanSpace ℂ ι) = 0
  · simp [h0]
  · simp only [h0, if_false, add_zero]
    rw [hform]
    calc _ ≤ K * Real.exp (-(q * Real.pi / 4 / 2) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) := hle
      _ ≤ K * Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16) := by
        gcongr

theorem gaussianInner_theta' (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (Y : GT ι) {q c : ℕ} {R0 : ℝ}
    (hq : 1 ≤ q) (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (hR : 16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2)
    {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (hG : G ∈ paPoly c) :
    HasSum (fun γ : lat Y.b => Y.ka γ * paIP q (paU q γ F) G) (paIP q (paTh Y q F) G) := by
  have := lat_countable Y.b
  obtain ⟨C, hC, hU⟩ := paU_int hq hF hG
  set f : lat Y.b → EuclideanSpace ℂ ι → ℂ := fun γ v =>
    Y.ka γ * paU q γ F v * (starRingEnd ℂ) (G v) * (paW q v : ℂ) with hf
  have hnorm : ∀ γ : lat Y.b, ∀ v, ‖f γ v‖ = ‖paU q γ F v‖ * ‖G v‖ * paW q v := by
    intro γ v
    simp only [hf, norm_mul, Y.ka_abs γ γ.2, one_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (paW_pos q v)]
  have hint : ∀ γ : lat Y.b, Integrable (f γ) := by
    intro γ
    have hcont : Continuous (f γ) := by
      simp only [hf]
      exact ((continuous_const.mul (paU_continuous _ hF)).mul
        (Complex.continuous_conj.comp (paPoly_continuous hG))).mul
        (Complex.continuous_ofReal.comp (paW_continuous q))
    exact ((hU γ).1).mono' hcont.aestronglyMeasurable (ae_of_all _ fun v => (hnorm γ v).le)
  have hsum : Summable fun γ : lat Y.b => ∫ v, ‖f γ v‖ := by
    refine Summable.of_nonneg_of_le (fun γ => integral_nonneg fun v => norm_nonneg _) (fun γ => ?_)
      ((lat_summable hP hA Y (c := c) hq hR0 hlat hR).mul_left C)
    simp_rw [hnorm]
    exact (hU γ).2
  have key := hasSum_integral_of_summable_integral_norm hint hsum
  have h1 : ∀ γ : lat Y.b, ∫ v, f γ v = Y.ka γ * paIP q (paU q γ F) G := by
    intro γ
    simp only [hf, paIP, mul_assoc]
    rw [integral_const_mul]
  have h2 : ∫ v, ∑' γ, f γ v = paIP q (paTh Y q F) G := by
    simp only [hf, paIP, paTh]
    congr 1
    funext v
    rw [tsum_mul_right, tsum_mul_right]
  rw [h2] at key
  have hfun : (fun γ : lat Y.b => Y.ka γ * paIP q (paU q γ F) G) = fun γ => ∫ v, f γ v :=
    funext fun γ => (h1 γ).symm
  rw [hfun]
  exact key

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
