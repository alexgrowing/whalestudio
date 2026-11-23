import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ThresholdGeDimension

namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField MeasureTheory
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace Col

variable {E : Type} [Field E] [NumberField E]

theorem cont_uc {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) : Continuous (uc K) := by
  have hz : ∀ k, Continuous (fun v : EuclideanSpace ℂ ι => Hf v (e K k)) := fun k => by
    have : (fun v : EuclideanSpace ℂ ι => Hf v (e K k)) = fun v => ⟪e K k, v⟫_ℂ :=
      funext fun v => Hf_eq_inner v _
    rw [this]; exact continuous_const.inner continuous_id
  unfold uc z
  exact continuous_finsetSum _ fun k _ => (Complex.continuous_im.comp (hz k)).smul continuous_const

theorem cont_jj {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) : Continuous (jj K) :=
  continuous_subtype_val.comp (ob2 K).repr.symm.continuous

def wc (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (c : Qc X I) (v : Vsp X.dim) : ℝ :=
  Real.exp (-(q * Real.pi) * ‖uc (IR I) v - uQ X I c‖ ^ 2)

def AE (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (v : Vsp X.dim) : ℝ≥0∞ :=
  ∑' c : Qc X I, ENNReal.ofReal (wc X I q c v)

instance (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : Countable (Qc X I) :=
  (Submodule.mkQ_surjective (NIp X I)).countable

section Avg

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  (hP : Ext.PackingCount) (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ)

def PhiE (v : Vsp X.dim) : ℝ≥0∞ :=
  ∑' c : Qc X I, ENNReal.ofReal (wc X I P.q c v *
    (YB hI hP P.q).ptN2 P.q β (wmap (IR I) (v - ((Quotient.out c : X.L) : Vsp X.dim))))

variable {β} (hβ : β ∈ (YB hI hP P.q).Sec P.q)
include hβ

theorem term_shift (γ : X.L) (c : Qc X I) (v : Vsp X.dim) :
    wc X I P.q c (v + γ) * (YB hI hP P.q).ptN2 P.q β
        (wmap (IR I) (v + γ - ((Quotient.out c : X.L) : Vsp X.dim))) =
      wc X I P.q (c - Submodule.Quotient.mk γ) v * (YB hI hP P.q).ptN2 P.q β
        (wmap (IR I) (v - ((Quotient.out (c - Submodule.Quotient.mk γ) : X.L) : Vsp X.dim))) := by
  have hK := hK_of hI
  congr 1
  · simp only [wc, map_sub, uQ_mk, uc_add]
    congr 3; abel
  · set c' := c - Submodule.Quotient.mk γ
    have hcl : (Quotient.out c' : X.L) - ((Quotient.out c : X.L) - γ) ∈ NIp X I := by
      rw [← Submodule.Quotient.eq]
      rw [Submodule.Quotient.mk_sub]
      change Submodule.Quotient.mk (Quotient.out c') = Submodule.Quotient.mk (Quotient.out c) - _
      rw [show (Submodule.Quotient.mk (Quotient.out c') : Qc X I) = c' from Quotient.out_eq' c',
        show (Submodule.Quotient.mk (Quotient.out c) : Qc X I) = c from Quotient.out_eq' c]
    set d : Vsp X.dim := (((Quotient.out c' : X.L) - ((Quotient.out c : X.L) - γ) : X.L) : Vsp X.dim)
    have hd : d ∈ Ip X I := hcl
    have hlat : -wmap (IR I) d ∈ lat (YB hI hP P.q).b :=
      (YB_lat hI hP P.q).2 (neg_mem (wmap_mem_GB hd))
    have e : wmap (IR I) (v - ((Quotient.out c' : X.L) : Vsp X.dim)) =
        -wmap (IR I) d + wmap (IR I) (v + γ - ((Quotient.out c : X.L) : Vsp X.dim)) := by
      rw [← map_neg, ← map_add]; congr 1; simp only [d, Submodule.coe_sub]; abel
    rw [e, lemS_periodic _ _ hβ hlat]

theorem PhiE_periodic (γ : Vsp X.dim) (hγ : γ ∈ X.L) (v : Vsp X.dim) :
    PhiE hI hP β (v + γ) = PhiE hI hP β v := by
  unfold PhiE
  have := fun c => term_shift hI hP hβ ⟨γ, hγ⟩ c v
  simp only at this
  simp_rw [this]
  exact (Equiv.subRight (Submodule.Quotient.mk (⟨γ, hγ⟩ : X.L) : Qc X I)).tsum_eq
    (fun c => ENNReal.ofReal (wc X I P.q c v * (YB hI hP P.q).ptN2 P.q β
      (wmap (IR I) (v - ((Quotient.out c : X.L) : Vsp X.dim)))))

theorem continuous_pointNormSq_quotient : Continuous ((YB hI hP P.q).ptN2 P.q β) := by
  unfold GT.ptN2
  exact (hβ.1.continuous.norm.pow 2).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))

omit hβ in
theorem cont_wc (c : Qc X I) : Continuous (wc X I P.q c) := by
  unfold wc
  exact Real.continuous_exp.comp (continuous_const.mul (((cont_uc _).sub continuous_const).norm.pow 2))

theorem meas_PhiE : Measurable (PhiE hI hP β) := by
  unfold PhiE
  refine Measurable.ennreal_tsum fun c => ?_
  refine Continuous.measurable ?_ |>.ennreal_ofReal
  exact (cont_wc c).mul ((continuous_pointNormSq_quotient hI hP hβ).comp
    ((wmap (IR I)).continuous.comp (continuous_id.sub continuous_const)))

omit hβ in
theorem meas_AE : Measurable (AE X I P.q) :=
  Measurable.ennreal_tsum fun c => (cont_wc c).measurable.ennreal_ofReal

omit hβ in
theorem wc_nonneg (c : Qc X I) (v : Vsp X.dim) : 0 ≤ wc X I P.q c v := (Real.exp_pos _).le

theorem PhiE_jj (v : Vsp X.dim) (t : EuclideanSpace ℂ (Fin (gB (IR I)))) :
    PhiE hI hP β (v + jj (IR I) t) = ∑' c : Qc X I, ENNReal.ofReal (wc X I P.q c v *
      (YB hI hP P.q).ptN2 P.q β (wmap (IR I) (v - ((Quotient.out c : X.L) : Vsp X.dim)) + t)) := by
  unfold PhiE
  congr 1; funext c
  have hu : uc (IR I) (v + jj (IR I) t) = uc (IR I) v := by
    rw [uc_add]; simp [uc, z_jj]
  have hw : wmap (IR I) (v + jj (IR I) t - ((Quotient.out c : X.L) : Vsp X.dim)) =
      wmap (IR I) (v - ((Quotient.out c : X.L) : Vsp X.dim)) + t := by
    rw [show v + jj (IR I) t - ((Quotient.out c : X.L) : Vsp X.dim) =
      (v - ((Quotient.out c : X.L) : Vsp X.dim)) + jj (IR I) t by abel, map_add, wmap_jj]
  simp only [wc, hu, hw]

theorem int_PhiE_jj (v : Vsp X.dim) :
    ∫⁻ t in ZSpan.fundamentalDomain (YB hI hP P.q).b, PhiE hI hP β (v + jj (IR I) t) =
      AE X I P.q v * ∫⁻ t in ZSpan.fundamentalDomain (YB hI hP P.q).b,
        ENNReal.ofReal ((YB hI hP P.q).ptN2 P.q β t) := by
  simp only [PhiE_jj hI hP hβ]
  have hc := continuous_pointNormSq_quotient hI hP hβ
  rw [lintegral_tsum (fun c => (Continuous.measurable (by fun_prop : Continuous fun t =>
      wc X I P.q c v * (YB hI hP P.q).ptN2 P.q β
        (wmap (IR I) (v - ((Quotient.out c : X.L) : Vsp X.dim)) + t))).ennreal_ofReal.aemeasurable)]
  simp_rw [ENNReal.ofReal_mul (wc_nonneg _ v)]
  have hsh : ∀ a : EuclideanSpace ℂ (Fin (gB (IR I))),
      ∫⁻ t in ZSpan.fundamentalDomain (YB hI hP P.q).b, ENNReal.ofReal ((YB hI hP P.q).ptN2 P.q β (a + t)) =
        ∫⁻ t in ZSpan.fundamentalDomain (YB hI hP P.q).b, ENNReal.ofReal ((YB hI hP P.q).ptN2 P.q β t) := by
    intro a
    simp_rw [add_comm a]
    exact lint_fd_shift (YB hI hP P.q).b (fun t => ENNReal.ofReal ((YB hI hP P.q).ptN2 P.q β t))
      (fun γ hγ x => by beta_reduce; rw [add_comm x γ, lemS_periodic _ _ hβ hγ]) a
  have hterm : ∀ c : Qc X I, ∫⁻ t in ZSpan.fundamentalDomain (YB hI hP P.q).b,
      ENNReal.ofReal (wc X I P.q c v) * ENNReal.ofReal ((YB hI hP P.q).ptN2 P.q β
        (wmap (IR I) (v - ((Quotient.out c : X.L) : Vsp X.dim)) + t)) =
      ENNReal.ofReal (wc X I P.q c v) * ∫⁻ t in ZSpan.fundamentalDomain (YB hI hP P.q).b,
        ENNReal.ofReal ((YB hI hP P.q).ptN2 P.q β t) := by
    intro c
    rw [lintegral_const_mul _ ((by fun_prop : Continuous fun t => (YB hI hP P.q).ptN2 P.q β
        (wmap (IR I) (v - ((Quotient.out c : X.L) : Vsp X.dim)) + t)).measurable.ennreal_ofReal), hsh]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_right]
  rfl

theorem avg_eq :
    (∫⁻ v in ZSpan.fundamentalDomain X.b, PhiE hI hP β v) *
        volume (ZSpan.fundamentalDomain (YB hI hP P.q).b) =
      (∫⁻ v in ZSpan.fundamentalDomain X.b, AE X I P.q v) *
        ∫⁻ t in ZSpan.fundamentalDomain (YB hI hP P.q).b, ENNReal.ofReal ((YB hI hP P.q).ptN2 P.q β t) := by
  have hmP := meas_PhiE hI hP hβ
  have hmeas : Measurable (Function.uncurry fun (v : Vsp X.dim)
      (t : EuclideanSpace ℂ (Fin (gB (IR I)))) => PhiE hI hP β (v + jj (IR I) t)) :=
    hmP.comp (continuous_fst.add ((cont_jj _).comp continuous_snd)).measurable
  have hswap := lintegral_lintegral_swap (μ := volume.restrict (ZSpan.fundamentalDomain X.b))
    (ν := volume.restrict (ZSpan.fundamentalDomain (YB hI hP P.q).b)) hmeas.aemeasurable
  simp only [int_PhiE_jj hI hP hβ] at hswap
  have hT : ∀ t, ∫⁻ v in ZSpan.fundamentalDomain X.b, PhiE hI hP β (v + jj (IR I) t) =
      ∫⁻ v in ZSpan.fundamentalDomain X.b, PhiE hI hP β v :=
    fun t => lint_fd_shift X.b _ (fun γ hγ x => PhiE_periodic hI hP hβ γ hγ x) _
  simp only [hT, lintegral_const, Measure.restrict_apply_univ] at hswap
  rw [← hswap, lintegral_mul_const _ (meas_AE (P := P))]

end Avg

section Fin

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) {β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ}
  (hβ : β ∈ (YB hI hP P.q).Sec P.q) {B : ℝ} (hB0 : 0 ≤ B)
  (hB : ∀ t, ‖β t‖ ^ 2 * Real.exp (-(P.q * Real.pi) * ‖t‖ ^ 2) ≤ B ^ 2)
include hI hP hA hβ hB0 hB

theorem AE_le_two (x : Vsp X.dim) : AE X I P.q x ≤ 2 := by
  obtain ⟨hs, hle⟩ := sum_w_le hI hP hA (uc (IR I) x)
  unfold AE wc
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le) hs]
  calc ENNReal.ofReal _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hle
    _ = 2 := by norm_num

theorem ptwise (x : Vsp X.dim) :
    ENNReal.ofReal (‖sP X I P.q β x‖ ^ 2 * Real.exp (-(P.q * Real.pi) * ‖x‖ ^ 2)) ≤ 2 * PhiE hI hP β x := by
  obtain ⟨hs, hle⟩ := sum_w_le hI hP hA (uc (IR I) x)
  set w : Qc X I → ℝ := fun c => wc X I P.q c x with hw
  set N : Qc X I → ℝ := fun c => ‖β (wmap (IR I) (x - ((Quotient.out c : X.L) : Vsp X.dim)))‖ *
    Real.exp (-(P.q * Real.pi) * ‖wmap (IR I) (x - ((Quotient.out c : X.L) : Vsp X.dim))‖ ^ 2 / 2) with hN
  have hw0 : ∀ c, 0 ≤ w c := fun c => (Real.exp_pos _).le
  have hN0 : ∀ c, 0 ≤ N c := fun c => by positivity
  have hN2 : ∀ c, N c ^ 2 = (YB hI hP P.q).ptN2 P.q β (wmap (IR I) (x - ((Quotient.out c : X.L) : Vsp X.dim))) := by
    intro c
    simp only [hN, GT.ptN2, mul_pow, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have hNB : ∀ c, N c ≤ B := by
    intro c
    have h := hB (wmap (IR I) (x - ((Quotient.out c : X.L) : Vsp X.dim)))
    have h2 := hN2 c
    unfold GT.ptN2 at h2
    rw [← h2] at h
    exact (pow_le_pow_iff_left₀ (hN0 c) hB0 two_ne_zero).1 h
  have hw_s : Summable w := hs
  have hwN2 : Summable (fun c => w c * N c ^ 2) :=
    Summable.of_nonneg_of_le (fun c => mul_nonneg (hw0 c) (sq_nonneg _))
      (fun c => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hN0 c) (hNB c) 2) (hw0 c)) (hw_s.mul_right _)
  have hwN : Summable (fun c => w c * N c) :=
    Summable.of_nonneg_of_le (fun c => mul_nonneg (hw0 c) (hN0 c))
      (fun c => mul_le_mul_of_nonneg_left (hNB c) (hw0 c)) (hw_s.mul_right _)
  have hT : ∀ c, ‖Tc X I P.q β c x‖ = Real.exp (P.q * Real.pi * ‖x‖ ^ 2 / 2) * (w c * N c) := by
    intro c
    rw [Tc, norm_Tm hI, uc_sub, ← uQ_out]
    simp only [hw, hN, wc]; ring
  have hTs : Summable (fun c => ‖Tc X I P.q β c x‖) := by
    simp only [hT]; exact hwN.mul_left _
  have hnorm : ‖sP X I P.q β x‖ ≤ Real.exp (P.q * Real.pi * ‖x‖ ^ 2 / 2) * ∑' c, w c * N c := by
    refine (norm_tsum_le_tsum_norm hTs).trans (le_of_eq ?_)
    simp only [hT, tsum_mul_left]
  have hcs := cs_tsum w N hw0 hN0 hw_s hwN2 hwN
  have hf : ‖sP X I P.q β x‖ ^ 2 * Real.exp (-(P.q * Real.pi) * ‖x‖ ^ 2) ≤
      2 * ∑' c, w c * N c ^ 2 := by
    set E1 := Real.exp (P.q * Real.pi * ‖x‖ ^ 2 / 2)
    have hE : E1 ^ 2 * Real.exp (-(P.q * Real.pi) * ‖x‖ ^ 2) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add,
        show ((2 : ℕ) : ℝ) * (P.q * Real.pi * ‖x‖ ^ 2 / 2) + -(P.q * Real.pi) * ‖x‖ ^ 2 = 0 by
          push_cast; ring, Real.exp_zero]
    have hS0 : 0 ≤ ∑' c, w c * N c := tsum_nonneg fun c => mul_nonneg (hw0 c) (hN0 c)
    have h1 : ‖sP X I P.q β x‖ ^ 2 ≤ (E1 * ∑' c, w c * N c) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    calc ‖sP X I P.q β x‖ ^ 2 * Real.exp (-(P.q * Real.pi) * ‖x‖ ^ 2)
        ≤ (E1 * ∑' c, w c * N c) ^ 2 * Real.exp (-(P.q * Real.pi) * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = (∑' c, w c * N c) ^ 2 * (E1 ^ 2 * Real.exp (-(P.q * Real.pi) * ‖x‖ ^ 2)) := by ring
      _ = (∑' c, w c * N c) ^ 2 := by rw [hE, mul_one]
      _ ≤ (∑' c, w c) * ∑' c, w c * N c ^ 2 := hcs
      _ ≤ 2 * ∑' c, w c * N c ^ 2 :=
          mul_le_mul_of_nonneg_right hle (tsum_nonneg fun c => mul_nonneg (hw0 c) (sq_nonneg _))
  refine (ENNReal.ofReal_le_ofReal hf).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_tsum_of_nonneg (fun c => mul_nonneg (hw0 c) (sq_nonneg _)) hwN2]
  unfold PhiE
  simp only [hN2, hw]

theorem l2_colS_le_four_mul : X.l2 P.q (colS X I P.q β) ≤ 4 * (YB hI hP P.q).l2 P.q β := by
  set D := ZSpan.fundamentalDomain X.b with hD
  set DB := ZSpan.fundamentalDomain (YB hI hP P.q).b with hDB
  have hm0 : volume D ≠ 0 := ZSpan.measure_fundamentalDomain_ne_zero X.b
  have hmt : volume D ≠ ∞ := (ZSpan.fundamentalDomain_isBounded X.b).measure_lt_top.ne
  have hn0 : volume DB ≠ 0 := ZSpan.measure_fundamentalDomain_ne_zero (YB hI hP P.q).b
  have hnt : volume DB ≠ ∞ := (ZSpan.fundamentalDomain_isBounded (YB hI hP P.q).b).measure_lt_top.ne
  set f : Vsp X.dim → ℝ := fun x => ‖sP X I P.q β x‖ ^ 2 * Real.exp (-(P.q * Real.pi) * ‖x‖ ^ 2) with hf
  have hcont : Continuous f :=
    ((diff_sP hI hP hA hB0 hB hβ.1).continuous.norm.pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  have hf0 : ∀ x, 0 ≤ f x := fun x => by positivity
  have hl2 : X.l2 P.q (colS X I P.q β) = ⨍ x in D, f x := by
    rw [l2_norm_fundamental_domain]
    congr 1; funext x
    simp only [PT.ptN2, colS, HC, Fin.sum_univ_one, Hf_self_re, hf]
  set hfun : EuclideanSpace ℂ (Fin (gB (IR I))) → ℝ := (YB hI hP P.q).ptN2 P.q β with hhfun
  have hc2 : Continuous hfun := continuous_pointNormSq_quotient hI hP hβ
  have hh0 : ∀ t, 0 ≤ hfun t := fun t => by simp only [hhfun, GT.ptN2]; positivity
  have hYl2 : (YB hI hP P.q).l2 P.q β = ⨍ t in DB, hfun t := rfl
  rw [hl2, hYl2, setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hcont.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hh0) hc2.aestronglyMeasurable,
    measureReal_def, measureReal_def]
  set a := ∫⁻ x in D, ENNReal.ofReal (f x)
  set h := ∫⁻ t in DB, ENNReal.ofReal (hfun t)
  set m := volume D
  set n := volume DB
  have ha : a ≤ 2 * ∫⁻ x in D, PhiE hI hP β x := by
    refine (lintegral_mono fun x => ptwise hI hP hA hβ hB0 hB x).trans (le_of_eq ?_)
    exact lintegral_const_mul 2 (meas_PhiE hI hP hβ)
  have hα : ∫⁻ x in D, AE X I P.q x ≤ 2 * m := by
    refine (lintegral_mono fun x => AE_le_two hI hP hA hβ hB0 hB x).trans (le_of_eq ?_)
    rw [lintegral_const, Measure.restrict_apply_univ]
  have hh : h ≤ ENNReal.ofReal (B ^ 2) * n := by
    refine (lintegral_mono fun t => ENNReal.ofReal_le_ofReal (hB t)).trans (le_of_eq ?_)
    rw [lintegral_const, Measure.restrict_apply_univ]
  have hht : h ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hnt) hh
  have havg := avg_eq hI hP hβ
  have key : a * n ≤ 4 * m * h := by
    calc a * n ≤ (2 * ∫⁻ x in D, PhiE hI hP β x) * n := by gcongr
      _ = 2 * ((∫⁻ x in D, AE X I P.q x) * h) := by rw [mul_assoc, havg]
      _ ≤ 2 * ((2 * m) * h) := by gcongr
      _ = 4 * m * h := by ring
  have hRt : 4 * m * h ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hmt) hht
  have keyR : a.toReal * n.toReal ≤ 4 * m.toReal * h.toReal := by
    have := ENNReal.toReal_mono hRt key
    simpa [ENNReal.toReal_mul] using this
  have hmR : 0 < m.toReal := ENNReal.toReal_pos hm0 hmt
  have hnR : 0 < n.toReal := ENNReal.toReal_pos hn0 hnt
  calc m.toReal⁻¹ * a.toReal = (a.toReal * n.toReal) / (m.toReal * n.toReal) := by
        field_simp
    _ ≤ (4 * m.toReal * h.toReal) / (m.toReal * n.toReal) :=
        div_le_div_of_nonneg_right keyR (by positivity)
    _ = 4 * (n.toReal⁻¹ * h.toReal) := by field_simp

end Fin

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
