import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.HfNegRight
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw

noncomputable section

namespace GlobalTheory.ThetaExist

theorem coeff_eq_zero_of_orthonormal {C H κ : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : C →L[ℂ] H) (e : κ → C)
    (h : Orthonormal ℂ fun i => T (e i)) {c : κ → ℂ} (hs : HasSum (fun i => c i • e i) 0)
    (k : κ) : c k = 0 := by
  classical
  have h1 := ((innerSL ℂ (T (e k))).comp T).hasSum hs
  simp only [ContinuousLinearMap.comp_apply, map_smul, innerSL_apply_apply, map_zero,
    orthonormal_iff_ite.1 h, smul_eq_mul, mul_ite, mul_one, mul_zero] at h1
  have h2 : HasSum (fun i => if k = i then c i else 0) (c k) := by
    convert hasSum_ite_eq k (c k) using 2 with i
    by_cases hi : k = i
    · simp [hi]
    · simp [hi, Ne.symm hi]
  exact h2.unique h1

theorem coeff_eq_zero_of_fourier {d : Type*} [Fintype d] {c : (d → ℤ) → ℂ}
    (hc : Summable fun n => ‖c n‖)
    (h0 : ∀ t : d → ℝ, ∑' n, c n * cexp (2 * Real.pi * I * ((∑ j, (n j : ℝ) * t j : ℝ) : ℂ)) = 0)
    (k : d → ℤ) : c k = 0 := by
  refine coeff_eq_zero_of_orthonormal _ UnitAddTorus.mFourier
    (UnitAddTorus.orthonormal_mFourier (d := d)) ?_ k
  have hs : Summable fun n => c n • UnitAddTorus.mFourier n :=
    .of_norm (by simpa [norm_smul, UnitAddTorus.mFourier_norm] using hc)
  suffices h : (0 : C(UnitAddTorus d, ℂ)) = ∑' n, c n • UnitAddTorus.mFourier n from
    h ▸ hs.hasSum
  ext x
  have hx : ∃ t : d → ℝ, x = fun j => (t j : UnitAddCircle) := by
    choose t ht using fun j => QuotientAddGroup.mk_surjective (x j)
    exact ⟨t, funext fun j => (ht j).symm⟩
  obtain ⟨t, rfl⟩ := hx
  rw [← ContinuousMap.tsum_apply hs, ContinuousMap.zero_apply, ← h0 t]
  refine tsum_congr fun n => ?_
  simp only [ContinuousMap.smul_apply, smul_eq_mul, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    fourier_coe_apply, ← Complex.exp_sum]
  congr 2
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

variable {ι : Type} [Fintype ι]

def expH (w : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι → ℂ := fun v => cexp (Real.pi * Hf v w)

theorem differentiable_Hf (a : EuclideanSpace ℂ ι) :
    Differentiable ℂ fun v : EuclideanSpace ℂ ι => Hf v a := by
  simp_rw [FPw.Hf_eq_inner]
  exact (innerSL ℂ a).differentiable

theorem re_Hf_le (v a : EuclideanSpace ℂ ι) : (Hf v a).re ≤ ‖v‖ * ‖a‖ := by
  rw [FPw.Hf_eq_inner, mul_comm]
  exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)

theorem norm_term_le (Y : GT ι) (w : EuclideanSpace ℂ ι) {R : ℝ} (hw : ‖w‖ ≤ R) (γ : lat Y.b)
    {v : EuclideanSpace ℂ ι} (hv : ‖v‖ ≤ R) :
    ‖Y.ka γ * paU 1 γ (expH w) v‖ ≤ Real.exp (5 * Real.pi * R ^ 2) *
      Real.exp (-(Real.pi / 4) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) := by
  set g : EuclideanSpace ℂ ι := γ.1
  unfold paU expH
  rw [norm_mul, Y.ka_abs g γ.2, one_mul, ← Complex.exp_add, Complex.norm_exp, ← Real.exp_add,
    Real.exp_le_exp, Hf_self, sub_eq_add_neg v, Hf_add_left]
  have hR : 0 ≤ R := (norm_nonneg _).trans hw
  have h1 : (Hf v g).re ≤ R * ‖g‖ := (re_Hf_le v g).trans (by gcongr)
  have h2 : (Hf v w).re ≤ R * R := (re_Hf_le v w).trans (by gcongr)
  have h3 : (Hf (-g) w).re ≤ ‖g‖ * R := (re_Hf_le (-g) w).trans (by rw [norm_neg]; gcongr)
  have e : (((1 : ℕ) : ℂ) * Real.pi * Hf v g - ((1 : ℕ) : ℂ) * Real.pi * ((‖g‖ : ℝ) : ℂ) ^ 2 / 2 +
      Real.pi * (Hf v w + Hf (-g) w)).re =
      Real.pi * ((Hf v g).re - ‖g‖ ^ 2 / 2 + (Hf v w).re + (Hf (-g) w).re) := by
    simp only [← Complex.ofReal_pow]
    simp only [Nat.cast_one, one_mul, add_re, sub_re, re_ofReal_mul, div_ofNat_re, ofReal_re]
    ring
  rw [e]
  have : (Hf v g).re - ‖g‖ ^ 2 / 2 + (Hf v w).re + (Hf (-g) w).re ≤ 5 * R ^ 2 - ‖g‖ ^ 2 / 4 := by
    nlinarith [sq_nonneg (‖g‖ / 2 - 2 * R)]
  nlinarith [mul_le_mul_of_nonneg_left this Real.pi_pos.le]

theorem summable_gauss (Y : GT ι) {a : ℝ} (ha : 0 < a) :
    Summable fun γ : lat Y.b => Real.exp (-a * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) :=
  summable_lattice_exp_neg_mul_norm_sq (lat Y.b) ha

theorem differentiable_paTh (Y : GT ι) (w : EuclideanSpace ℂ ι) :
    Differentiable ℂ (paTh Y 1 (expH w)) := by
  rw [← differentiableOn_univ]
  refine SCV.differentiableOn_tsum_of_locally_normal
    (F := fun (γ : lat Y.b) v => Y.ka γ * paU 1 γ (expH w) v) isOpen_univ (fun γ => ?_)
    (fun x _ => ?_)
  · have h1 := differentiable_Hf (γ : EuclideanSpace ℂ ι)
    have h2 : Differentiable ℂ fun v : EuclideanSpace ℂ ι => Hf (v - γ.1) w :=
      (differentiable_Hf w).comp (differentiable_id.sub_const _)
    unfold paU expH
    refine Differentiable.differentiableOn ?_
    fun_prop
  · refine ⟨Metric.ball 0 (max (‖x‖ + 1) ‖w‖), Metric.isOpen_ball.mem_nhds ?_, _,
      (summable_gauss Y (a := Real.pi / 4) (by positivity)).mul_left _,
      fun γ z hz => norm_term_le Y w (le_max_right _ _) γ (mem_ball_zero_iff.1 hz).le⟩
    rw [mem_ball_zero_iff]
    exact lt_of_lt_of_le (lt_add_one _) (le_max_left _ _)

theorem paTh_centre (Y : GT ι) (v : EuclideanSpace ℂ ι) :
    paTh Y 1 (expH v) v = cexp (Real.pi * Hf v v) *
      ∑' γ : lat Y.b, (Y.ka γ * (Real.exp (-(Real.pi / 2) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) : ℝ)) *
        cexp (2 * Real.pi * I * ((Hf v γ).im : ℂ)) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  set g : EuclideanSpace ℂ ι := γ.1
  unfold paU expH
  rw [Hf_self g, sub_eq_add_neg v, Hf_add_left, Hf_neg_left, ← Hf_conj v g, conj_eq_sub (Hf v g),
    ← Complex.exp_add, Complex.ofReal_exp, mul_assoc (Y.ka g), ← Complex.exp_add,
    mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem exists_sec_ne_zero (Y : GT ι) (hC : Coc Y 1) : ∃ s ∈ Y.Sec 1, s ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hz : ∀ w, paTh Y 1 (expH w) = 0 := fun w =>
    hcon _ ⟨differentiable_paTh Y w, fun γ hγ v => paTh_add hC _ hγ v⟩
  set B := Y.b.restrictScalars ℤ with hB
  set c : lat Y.b → ℂ := fun γ =>
    Y.ka γ * (Real.exp (-(Real.pi / 2) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) : ℝ) with hc
  have hcs : Summable fun γ => ‖c γ‖ := by
    refine (summable_gauss Y (a := Real.pi / 2) (by positivity)).congr fun γ => ?_
    rw [hc]
    simp only [norm_mul, Y.ka_abs γ γ.2, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  choose x _ hx using fun j => Y.perfect (B.coord j).toAddMonoidHom
  have key := coeff_eq_zero_of_fourier (c := fun n => c (B.equivFun.symm n))
    ((B.equivFun.symm.toEquiv.summable_iff (f := fun γ => ‖c γ‖)).2 hcs) (fun t => ?_) 0
  · simp [hc, ka_zero hC] at key
  · set v : EuclideanSpace ℂ ι := ∑ j, (t j : ℂ) • x j with hv
    have h1 := paTh_centre Y v
    rw [hz v, Pi.zero_apply, eq_comm, mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)] at h1
    rw [← h1, ← B.equivFun.symm.toEquiv.tsum_eq]
    refine tsum_congr fun n => ?_
    have h2 : ∀ j, (Hf (x j) (B.equivFun.symm n : lat Y.b)).im = n j := fun j => by
      rw [← hx j]
      simp [Finsupp.single_apply]
    suffices h3 : ∑ j, (n j : ℝ) * t j = (Hf v (B.equivFun.symm n : lat Y.b)).im by
      rw [h3]; rfl
    simp only [FPw.Hf_eq_inner] at h2 ⊢
    rw [hv, inner_sum, Complex.im_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right, Complex.im_ofReal_mul, h2, mul_comm]

theorem exists_theta_ne_zero (E : Type) [Field E] [NumberField E] (X : PT E) :
    ∃ s ∈ X.Sec 1 1, s ≠ 0 := by
  let Y : GT (Idx X.dim) :=
    { b := X.b
      integral := X.integral
      perfect := X.perfect
      ka := fun γ => (X.eps γ : ℂ)
      ka_abs := fun x hx => by rcases X.eps_pm x hx with h | h <;> simp [h] }
  have hC : Coc Y 1 := by
    intro γ hγ δ hδ
    obtain ⟨k, hk⟩ := X.integral γ δ hγ hδ
    have h := congrArg (fun r : ℝ => (r : ℂ)) (X.eps_add γ hγ δ hδ)
    change ((X.eps (γ + δ) : ℤ) : ℂ) = (X.eps γ : ℂ) * (X.eps δ : ℂ) * _
    rw [hk] at h ⊢
    have hs : Complex.sin (-(Real.pi * (1 : ℕ) * ((k : ℝ) : ℂ))) = 0 := by
      rw [Complex.sin_neg]
      simpa [mul_comm] using Complex.sin_int_mul_pi k
    rw [Complex.exp_mul_I, hs, Complex.cos_neg]
    simpa using h
  obtain ⟨s, ⟨hd, hs⟩, hne⟩ := exists_sec_ne_zero Y hC
  refine ⟨fun v => s (v 0), ⟨hd.comp (differentiable_apply 0), fun γ hγ v => ?_⟩, fun h => hne ?_⟩
  · have := hs (γ 0) (hγ 0) (v 0)
    simpa [HC, Y] using this
  · funext z
    exact congrFun h fun _ => z

end GlobalTheory.ThetaExist
