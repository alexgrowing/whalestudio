import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.TrDefs
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.HasFDerivAtPm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorExplicitFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodUnipotentOfParts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Qf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightDifferentiableLogarithmicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarizationCoordinateDerivativeBoundsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightMajorantBoundStatement

noncomputable section

open MeasureTheory Matrix Ad3.LR Ad3.LR.DTr Topology

namespace GlobalTheory.CompanionTheory.DInt2

theorem continuous_det : Continuous (fun h : M22 => (Matrix.of h).det) := by
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  fun_prop

theorem isOpen_pos : IsOpen {h : M22 | 0 < (Matrix.of h).det} :=
  isOpen_lt continuous_const continuous_det

theorem isOpen_neg : IsOpen {h : M22 | (Matrix.of h).det < 0} :=
  isOpen_lt continuous_det continuous_const

theorem inn_eq (Φ : Sw) (g : GL (Fin 3) ℝ) (h : M22) :
    inn Φ g (Matrix.of h) = Ad3.LR.B.innB (Ad3.LR.B.rt g Φ) h 1 := by
  simp [inn, Ad3.LR.B.innB, Ad3.LR.B.rt]

theorem inn_bound (N : ℕ) (Φ : Sw) (g : GL (Fin 3) ℝ) : ∃ C : ℝ, ∀ h : M22, (Matrix.of h).det ≠ 0 →
    ‖inn Φ g (Matrix.of h)‖ ≤ C * |(Matrix.of h).det|⁻¹ / ((1 + ‖h‖) ^ N * (1 + ‖Ad3.LR.B.eta h‖) ^ N) := by
  obtain ⟨C, hC⟩ := Ad3.LR.B.ibpBound N
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.PerUAssembled.schwartz_bounds (GlobalTheory.CompanionTheory.PerUAssembled.rtS g Φ) (N + 8)
  rw [GlobalTheory.CompanionTheory.PerUAssembled.rtS_coe] at hB
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (Ad3.LR.B.rt g Φ) := by
    have := (GlobalTheory.CompanionTheory.PerUAssembled.rtS g Φ).smooth ⊤
    rwa [GlobalTheory.CompanionTheory.PerUAssembled.rtS_coe] at this
  refine ⟨C * B, fun h hdet => ?_⟩
  rw [inn_eq]
  have := hC (Ad3.LR.B.rt g Φ) B hsm (fun n hn X => hB n (by omega) X) h 1 hdet
  simpa using this

theorem inn_meas (Φ : Sw) (g : GL (Fin 3) ℝ) :
    AEStronglyMeasurable (fun h : M22 => inn Φ g (Matrix.of h)) volume := by
  have hb : Continuous (fun x : Fin 2 → ℝ => blk x) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [blk] <;> fun_prop
  have ho : Continuous (fun h : M22 => Matrix.of h) := continuous_id
  have hM : Continuous (fun p : M22 × (Fin 2 → ℝ) =>
      Matrix.of p.1 * blk p.2 * (g : Matrix (Fin 3) (Fin 3) ℝ)) :=
    ((ho.comp continuous_fst).matrix_mul (hb.comp continuous_snd)).matrix_mul continuous_const
  have hs : Continuous (fun p : M22 × (Fin 2 → ℝ) =>
      (Matrix.of.symm (Matrix.of p.1 * blk p.2 * (g : Matrix (Fin 3) (Fin 3) ℝ)) : M23)) := hM
  have hp : Continuous (fun p : M22 × (Fin 2 → ℝ) => Ad3.psiR (-(p.2 1))) := by
    unfold Ad3.psiR
    fun_prop
  have hc : Continuous (fun p : M22 × (Fin 2 → ℝ) =>
      Φ (Matrix.of.symm (Matrix.of p.1 * blk p.2 * (g : Matrix (Fin 3) (Fin 3) ℝ))) * Ad3.psiR (-(p.2 1))) :=
    (Φ.continuous.comp hs).mul hp
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable

theorem al_rpol (a b : Fin 2) (h : M22) :
    al (rpol a b h) = (if b = 0 then 1 else Complex.I) * (h a 0 : ℂ) := by
  fin_cases b <;> simp [al, rpol, mul_comm]

theorem be_rpol (a b : Fin 2) (h : M22) :
    be (rpol a b h) = (if b = 0 then 1 else Complex.I) * (h a 1 : ℂ) := by
  fin_cases b <;> simp [be, rpol, mul_comm]

theorem dd_rpol (a b : Fin 2) (h : M22) :
    dd h (rpol a b h) = if a = b then (Matrix.of h).det else 0 := by
  rw [Matrix.det_fin_two]
  fin_cases a <;> fin_cases b <;> simp [dd, rpol] <;> ring

theorem cross_rpol (a b : Fin 2) (h : M22) :
    be (rpol a b h) * al h - be h * al (rpol a b h) = kap a b * (((Matrix.of h).det : ℝ) : ℂ) := by
  rw [al_rpol, be_rpol, Matrix.det_fin_two]
  fin_cases a <;> fin_cases b <;> simp [al, be, kap] <;> ring_nf <;> simp <;> ring

theorem al_ne (h : M22) (hd : 0 < (Matrix.of h).det) : al h ≠ 0 :=
  GlobalTheory.CompanionTheory.WeightClosed.alpha_ne_zero h hd

theorem ell_rpol (k : ℕ) (a b : Fin 2) (h : M22) (hd : 0 < (Matrix.of h).det) :
    ell k h (rpol a b h) = (if a = b then (k : ℂ) - 1 else 0) + (1 - 2 * (k : ℂ)) * rho a b h +
      2 * Real.pi * Complex.I * kap a b * tt h := by
  have hA := al_ne h hd
  have hD : (((Matrix.of h).det : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold ell rho tt
  rw [cross_rpol, dd_rpol]
  split_ifs
  · field_simp
  · simp only [Complex.ofReal_zero]
    field_simp
    ring

theorem norm_al_rpol_le (a b : Fin 2) (h : M22) : ‖al (rpol a b h)‖ ≤ ‖al h‖ := by
  rw [al_rpol, norm_mul]
  have h1 : ‖(if b = 0 then (1 : ℂ) else Complex.I)‖ = 1 := by split_ifs <;> simp
  rw [h1, one_mul, Complex.norm_real, Real.norm_eq_abs]
  fin_cases a
  · simpa [al] using Complex.abs_re_le_norm (al h)
  · simpa [al] using Complex.abs_im_le_norm (al h)

theorem norm_rho_le (c d : Fin 2) (h : M22) (hd : 0 < (Matrix.of h).det) : ‖rho c d h‖ ≤ 1 := by
  have hA := al_ne h hd
  unfold rho
  rw [norm_div]
  exact div_le_one_of_le₀ (norm_al_rpol_le c d h) (norm_nonneg _)

theorem norm_tt (h : M22) (hd : 0 < (Matrix.of h).det) : ‖tt h‖ = uu h := by
  unfold tt uu
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]

theorem uu_pos (h : M22) (hd : 0 < (Matrix.of h).det) : 0 < uu h := by
  have hA := al_ne h hd
  unfold uu
  have : 0 < ‖al h‖ := norm_pos_iff.2 hA
  positivity

theorem norm_kap (a b : Fin 2) : ‖kap a b‖ = 1 := by
  unfold kap
  fin_cases a <;> fin_cases b <;> simp

theorem weight_zero_not_pos_det (k : ℕ) (h : M22) (hd : ¬ 0 < (Matrix.of h).det) : w0 k h = 0 := by
  have : ¬ 0 < ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    simpa using hd
  unfold w0 Wm
  rw [if_neg this]
  simp

theorem weight_eventually_zero_neg_det (k : ℕ) (h : M22) (hd : (Matrix.of h).det < 0) : w0 k =ᶠ[𝓝 h] 0 := by
  filter_upwards [isOpen_neg.mem_nhds hd] with x hx
  exact weight_zero_not_pos_det k x (not_lt.2 (le_of_lt hx))

theorem measurable_al : Measurable al := by
  unfold al
  fun_prop

theorem measurable_be : Measurable be := by
  unfold be
  fun_prop

theorem measurable_w0_of_three_le (k : ℕ) (hk : 3 ≤ k) : Measurable (w0 k) := by
  have hdet : Measurable (fun h : M22 => (Matrix.of h).det) := continuous_det.measurable
  have hF : Measurable (fun h : M22 => (((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) *
      (al h) ^ (-(2 * (k : ℤ) - 1)) * Complex.exp (2 * Real.pi * Complex.I * (be h / al h))) := by
    have h1 := Complex.measurable_ofReal.comp hdet
    have h2 := measurable_al
    have h3 := measurable_be
    exact ((h1.pow_const _).mul (h2.pow_const _)).mul
      (Complex.measurable_exp.comp (measurable_const.mul (h3.div h2)))
  have hs : MeasurableSet {h : M22 | 0 < (Matrix.of h).det} := isOpen_pos.measurableSet
  have : w0 k = fun h : M22 => if 0 < (Matrix.of h).det then ((((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) *
      (al h) ^ (-(2 * (k : ℤ) - 1)) * Complex.exp (2 * Real.pi * Complex.I * (be h / al h))) else 0 := by
    funext h
    split_ifs with hd
    · exact GlobalTheory.CompanionTheory.WeightClosed.main k hk h hd
    · exact weight_zero_not_pos_det k h hd
  rw [this]
  exact Measurable.ite hs hF measurable_const

theorem measurable_Lt (v : ℂ) (a b : Fin 2) {w : M22 → ℂ} (hw : Measurable w) :
    Measurable (Lt v a b w) := by
  have hr : ∀ h : M22, rpol a b h = h a 0 • (rpol 0 b (fun i j => if i = 0 ∧ j = 0 then 1 else 0)) +
      h a 1 • (rpol 0 b (fun i j => if i = 0 ∧ j = 1 then 1 else 0)) := by
    intro h
    funext r c
    fin_cases c <;> by_cases hb : r = b <;> simp [rpol, hb]
  have hd : Measurable (fun h : M22 => fderiv ℝ w h (rpol a b h)) := by
    have : (fun h : M22 => fderiv ℝ w h (rpol a b h)) = fun h =>
        h a 0 • fderiv ℝ w h (rpol 0 b (fun i j => if i = 0 ∧ j = 0 then 1 else 0)) +
        h a 1 • fderiv ℝ w h (rpol 0 b (fun i j => if i = 0 ∧ j = 1 then 1 else 0)) := by
      funext h
      rw [hr h, map_add, map_smul, map_smul]
    rw [this]
    have m0 := measurable_fderiv_apply_const ℝ w (rpol 0 b (fun i j => if i = 0 ∧ j = 0 then (1 : ℝ) else 0))
    have m1 := measurable_fderiv_apply_const ℝ w (rpol 0 b (fun i j => if i = 0 ∧ j = 1 then (1 : ℝ) else 0))
    have c0 : Measurable (fun h : M22 => h a 0) := by fun_prop
    have c1 : Measurable (fun h : M22 => h a 1) := by fun_prop
    exact (c0.smul m0).add (c1.smul m1)
  unfold Lt Lop
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    fun_prop
  · simp only [hab, if_false]
    fun_prop

theorem Qf_deriv (k : ℕ) (v : ℂ) (a b c d : Fin 2) (h : M22) (hd : 0 < (Matrix.of h).det) :
    DifferentiableAt ℝ (Qf k v c d) h ∧ fderiv ℝ (Qf k v c d) h (rpol a b h) =
      (2 * (k : ℂ) - 1) * fderiv ℝ (rho c d) h (rpol a b h) -
        2 * Real.pi * Complex.I * kap c d * fderiv ℝ tt h (rpol a b h) := by
  obtain ⟨h1, h2, -, -⟩ := GlobalTheory.T.polarization_coordinate_derivative_bounds a b c d h hd
  have hq := ((h1.hasFDerivAt.const_mul (2 * (k : ℂ) - 1)).const_add
    (if c = d then v - 2 - ((k : ℂ) - 1) else 0)).sub
    (h2.hasFDerivAt.const_mul (2 * Real.pi * Complex.I * kap c d))
  have e : (fun y => (if c = d then v - 2 - ((k : ℂ) - 1) else 0) + (2 * (k : ℂ) - 1) * rho c d y -
      2 * Real.pi * Complex.I * kap c d * tt y) = Qf k v c d := rfl
  have hq' : HasFDerivAt (Qf k v c d) ((2 * (k : ℂ) - 1) • fderiv ℝ (rho c d) h -
      (2 * Real.pi * Complex.I * kap c d) • fderiv ℝ tt h) h := hq
  refine ⟨hq'.differentiableAt, ?_⟩
  rw [hq'.fderiv]
  simp

theorem first_derivative_weight_formula (k : ℕ) (hk : 3 ≤ k) (v : ℂ) (c d : Fin 2) (h : M22) (hd : 0 < (Matrix.of h).det) :
    Lt v c d (w0 k) h = w0 k h * Qf k v c d h := by
  unfold Lt Lop
  rw [(GlobalTheory.T.weight_differentiable_logarithmic k hk h hd).2, ell_rpol k c d h hd]
  unfold Qf
  split_ifs
  · ring
  · ring

theorem second_derivative_weight_formula (k : ℕ) (hk : 3 ≤ k) (v v' : ℂ) (a b c d : Fin 2) (h : M22)
    (hd : 0 < (Matrix.of h).det) :
    Lt v a b (Lt v' c d (w0 k)) h = w0 k h * ((if a = b then (v - 2) * Qf k v' c d h else 0) -
      fderiv ℝ (Qf k v' c d) h (rpol a b h) - Qf k v' c d h * ell k h (rpol a b h)) := by
  obtain ⟨hw, hw'⟩ := GlobalTheory.T.weight_differentiable_logarithmic k hk h hd
  obtain ⟨hq, -⟩ := Qf_deriv k v' a b c d h hd
  have he : Lt v' c d (w0 k) =ᶠ[𝓝 h] fun x => w0 k x * Qf k v' c d x := by
    filter_upwards [isOpen_pos.mem_nhds hd] with x hx
    exact first_derivative_weight_formula k hk v' c d x hx
  have hf : fderiv ℝ (fun x => w0 k x * Qf k v' c d x) h = w0 k h • fderiv ℝ (Qf k v' c d) h + Qf k v' c d h • fderiv ℝ (w0 k) h := (hw.hasFDerivAt.mul hq.hasFDerivAt).fderiv
  have e : fderiv ℝ (Lt v' c d (w0 k)) h (rpol a b h) =
      w0 k h * fderiv ℝ (Qf k v' c d) h (rpol a b h) +
        Qf k v' c d h * (w0 k h * ell k h (rpol a b h)) := by
    rw [he.fderiv_eq, hf]
    simp [hw']
  have e0 := first_derivative_weight_formula k hk v' c d h hd
  show (if a = b then v * Lt v' c d (w0 k) h else 0) + (-(fderiv ℝ (Lt v' c d (w0 k)) h (rpol a b h)) -
    2 * (if a = b then Lt v' c d (w0 k) h else 0)) = _
  rw [e, e0]
  split_ifs
  · ring
  · ring

theorem norm_ite_le (p : Prop) [Decidable p] (x : ℂ) : ‖(if p then x else 0)‖ ≤ ‖x‖ := by
  split_ifs <;> simp

theorem two_pi_le : 2 * Real.pi ≤ 8 := by linarith [Real.pi_lt_four]

def Pc (k : ℕ) (v : ℂ) : ℝ := ‖v‖ + 3 * k + 10

theorem norm_const (c d : Fin 2) (y : ℂ) : ‖2 * Real.pi * Complex.I * kap c d * y‖ ≤ 8 * ‖y‖ := by
  have e : ‖2 * Real.pi * Complex.I * kap c d * y‖ = 2 * Real.pi * ‖y‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_kap, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    simp
  rw [e]
  exact mul_le_mul_of_nonneg_right two_pi_le (norm_nonneg _)

theorem norm_two_k (k : ℕ) (hk : 3 ≤ k) : ‖(2 * (k : ℂ) - 1)‖ ≤ 2 * k := by
  have : (2 * (k : ℂ) - 1) = ((2 * (k : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  linarith

theorem norm_weight_exponent_le (k : ℕ) (hk : 3 ≤ k) : ‖((k : ℂ) - 1)‖ ≤ k := by
  have : ((k : ℂ) - 1) = (((k : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  linarith

theorem norm_Qf_le (k : ℕ) (hk : 3 ≤ k) (v : ℂ) (c d : Fin 2) (h : M22) (hd : 0 < (Matrix.of h).det) :
    ‖Qf k v c d h‖ ≤ Pc k v * (1 + uu h) := by
  have hu := (uu_pos h hd).le
  have h1 : ‖(if c = d then v - 2 - ((k : ℂ) - 1) else 0)‖ ≤ ‖v‖ + 2 + k := by
    refine (norm_ite_le _ _).trans ?_
    refine (norm_sub_le _ _).trans ?_
    have := norm_sub_le v 2
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    linarith [norm_weight_exponent_le k hk]
  have h2 : ‖(2 * (k : ℂ) - 1) * rho c d h‖ ≤ 2 * k := by
    rw [norm_mul]
    calc _ ≤ (2 * (k : ℝ)) * 1 := mul_le_mul (norm_two_k k hk) (norm_rho_le c d h hd) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have h3 := norm_const c d (tt h)
  rw [norm_tt h hd] at h3
  unfold Qf
  refine (norm_sub_le _ _).trans ?_
  have := norm_add_le (if c = d then v - 2 - ((k : ℂ) - 1) else 0) ((2 * (k : ℂ) - 1) * rho c d h)
  unfold Pc
  have hv := norm_nonneg v
  have hkk : (0 : ℝ) ≤ k := by positivity
  nlinarith [mul_nonneg hv hu, mul_nonneg hkk hu]

theorem norm_ell_le (k : ℕ) (hk : 3 ≤ k) (v : ℂ) (a b : Fin 2) (h : M22) (hd : 0 < (Matrix.of h).det) :
    ‖ell k h (rpol a b h)‖ ≤ Pc k v * (1 + uu h) := by
  have hu := (uu_pos h hd).le
  rw [ell_rpol k a b h hd]
  have h1 : ‖(if a = b then (k : ℂ) - 1 else 0)‖ ≤ k := (norm_ite_le _ _).trans (norm_weight_exponent_le k hk)
  have h2 : ‖(1 - 2 * (k : ℂ)) * rho a b h‖ ≤ 2 * k := by
    rw [norm_mul, show (1 - 2 * (k : ℂ)) = -(2 * (k : ℂ) - 1) by ring, norm_neg]
    calc _ ≤ (2 * (k : ℝ)) * 1 := mul_le_mul (norm_two_k k hk) (norm_rho_le a b h hd) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have h3 := norm_const a b (tt h)
  rw [norm_tt h hd] at h3
  refine (norm_add_le _ _).trans ?_
  have := norm_add_le (if a = b then (k : ℂ) - 1 else 0) ((1 - 2 * (k : ℂ)) * rho a b h)
  unfold Pc
  have hv := norm_nonneg v
  have hkk : (0 : ℝ) ≤ k := by positivity
  nlinarith [mul_nonneg hv hu, mul_nonneg hkk hu]

theorem norm_dQf_le (k : ℕ) (hk : 3 ≤ k) (v : ℂ) (a b c d : Fin 2) (h : M22) (hd : 0 < (Matrix.of h).det) :
    ‖fderiv ℝ (Qf k v c d) h (rpol a b h)‖ ≤ 3 * Pc k v * (1 + uu h) := by
  have hu := (uu_pos h hd).le
  obtain ⟨-, -, h1, h2⟩ := GlobalTheory.T.polarization_coordinate_derivative_bounds a b c d h hd
  rw [(Qf_deriv k v a b c d h hd).2]
  have h3 := norm_const c d (fderiv ℝ tt h (rpol a b h))
  have h4 : ‖(2 * (k : ℂ) - 1) * fderiv ℝ (rho c d) h (rpol a b h)‖ ≤ 2 * k * 2 := by
    rw [norm_mul]
    exact mul_le_mul (norm_two_k k hk) h1 (norm_nonneg _) (by positivity)
  refine (norm_sub_le _ _).trans ?_
  unfold Pc
  have hv := norm_nonneg v
  have hkk : (0 : ℝ) ≤ k := by positivity
  nlinarith [mul_nonneg hv hu, mul_nonneg hkk hu]

theorem bound2 (k : ℕ) (hk : 3 ≤ k) (v v' : ℂ) (a b c d : Fin 2) : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : M22,
    0 < (Matrix.of h).det → ‖Lt v a b (Lt v' c d (w0 k)) h‖ ≤ C * ((1 + uu h) ^ 2 * ‖w0 k h‖) := by
  have hP : 0 ≤ Pc k v' := by unfold Pc; positivity
  refine ⟨(‖v‖ + 2) * Pc k v' + 3 * Pc k v' + Pc k v' ^ 2, by positivity, fun h hd => ?_⟩
  have hu := (uu_pos h hd).le
  rw [second_derivative_weight_formula k hk v v' a b c d h hd, norm_mul, mul_comm ‖w0 k h‖, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hQ := norm_Qf_le k hk v' c d h hd
  have hE := norm_ell_le k hk v' a b h hd
  have hD := norm_dQf_le k hk v' a b c d h hd
  have h1 : ‖(if a = b then (v - 2) * Qf k v' c d h else 0)‖ ≤ (‖v‖ + 2) * (Pc k v' * (1 + uu h)) := by
    refine (norm_ite_le _ _).trans ?_
    rw [norm_mul]
    have : ‖v - 2‖ ≤ ‖v‖ + 2 := by simpa using norm_sub_le v 2
    exact mul_le_mul this hQ (norm_nonneg _) (by positivity)
  have h2 : ‖Qf k v' c d h * ell k h (rpol a b h)‖ ≤ (Pc k v' * (1 + uu h)) * (Pc k v' * (1 + uu h)) := by
    rw [norm_mul]
    exact mul_le_mul hQ hE (norm_nonneg _) (by positivity)
  refine (norm_sub_le _ _).trans ?_
  have h3 := norm_sub_le (if a = b then (v - 2) * Qf k v' c d h else 0) (fderiv ℝ (Qf k v' c d) h (rpol a b h))
  have hv := norm_nonneg v
  have hone : 1 + uu h ≤ (1 + uu h) ^ 2 := by nlinarith
  have t1 : (‖v‖ + 2) * (Pc k v' * (1 + uu h)) ≤ (‖v‖ + 2) * Pc k v' * (1 + uu h) ^ 2 := by
    rw [mul_assoc]
    gcongr
  have t2 : 3 * Pc k v' * (1 + uu h) ≤ 3 * Pc k v' * (1 + uu h) ^ 2 := by gcongr
  nlinarith

theorem vanish2 (k : ℕ) (v v' : ℂ) (a b c d : Fin 2) (h : M22) (hd : (Matrix.of h).det < 0) :
    Lt v a b (Lt v' c d (w0 k)) h = 0 := by
  have hz : ∀ x : M22, (Matrix.of x).det < 0 → Lt v' c d (w0 k) x = 0 := by
    intro x hx
    have e : fderiv ℝ (w0 k) x = fderiv ℝ 0 x := (weight_eventually_zero_neg_det k x hx).fderiv_eq
    have e0 := weight_zero_not_pos_det k x (not_lt.2 hx.le)
    unfold Lt Lop
    rw [e, e0]
    simp
  have he : Lt v' c d (w0 k) =ᶠ[𝓝 h] 0 := by
    filter_upwards [isOpen_neg.mem_nhds hd] with x hx
    exact hz x hx
  have e : fderiv ℝ (Lt v' c d (w0 k)) h = fderiv ℝ 0 h := he.fderiv_eq
  show (if a = b then v * Lt v' c d (w0 k) h else 0) + (-(fderiv ℝ (Lt v' c d (w0 k)) h (rpol a b h)) -
    2 * (if a = b then Lt v' c d (w0 k) h else 0)) = 0
  rw [e, hz h hd]
  simp

theorem maj_nonneg (k N : ℕ) (a b : ℝ) (h : M22) : 0 ≤ Ad3.LR.B.maj k N a b h := by
  unfold Ad3.LR.B.maj
  positivity

theorem main : Ad3.LR.B.MajScaled → Ad3.LR.DInt2 := by
  intro hMS k hk v v' a b c d Φ g
  obtain ⟨N, hN⟩ := hMS k hk 1 one_pos
  obtain ⟨C3, hC3⟩ := hN N le_rfl
  have hint := (hC3 (1 / 2) 1 (by norm_num) one_ne_zero).1
  obtain ⟨C1, hC1, hb⟩ := bound2 k hk v v' a b c d
  obtain ⟨C2, hm⟩ := GlobalTheory.T.weight_majorant_bound k hk
  obtain ⟨C4, hi⟩ := inn_bound N Φ g
  have hmeas : AEStronglyMeasurable (fun h : M22 => Lt v a b (Lt v' c d (w0 k)) h * inn Φ g (Matrix.of h)) volume :=
    ((measurable_Lt v a b (measurable_Lt v' c d (measurable_w0_of_three_le k hk))).aestronglyMeasurable).mul (inn_meas Φ g)
  refine Integrable.mono' (hint.const_mul (C1 * |C4| * |C2|)) hmeas ?_
  filter_upwards [GlobalTheory.CompanionTheory.PerUAssembled.ae_det_ne_zero] with h hdet
  have hmn := maj_nonneg k N (1 / 2) 1 h
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · rw [vanish2 k v v' a b c d h hneg, zero_mul, norm_zero]
    positivity
  · rw [norm_mul]
    have hden : 0 < (1 + ‖h‖) ^ N * (1 + ‖Ad3.LR.B.eta h‖) ^ N := by positivity
    have hI := hi h hdet
    have hB := hb h hpos
    have hM := hm N h hpos
    set Den := (1 + ‖h‖) ^ N * (1 + ‖Ad3.LR.B.eta h‖) ^ N with hDen
    set J := |(Matrix.of h).det|⁻¹ with hJ
    set P := (1 + uu h) ^ 2 * ‖w0 k h‖ with hPdef
    have hP : 0 ≤ P := by positivity
    have hJ0 : 0 ≤ J := by positivity
    calc ‖Lt v a b (Lt v' c d (w0 k)) h‖ * ‖inn Φ g (Matrix.of h)‖
        ≤ (C1 * P) * (|C4| * J / Den) := by
          refine mul_le_mul hB (hI.trans ?_) (norm_nonneg _) (by positivity)
          gcongr
          exact le_abs_self _
      _ = C1 * |C4| * (P * J / Den) := by ring
      _ ≤ C1 * |C4| * (|C2| * Ad3.LR.B.maj k N (1 / 2) 1 h) := by
          refine mul_le_mul_of_nonneg_left (hM.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_right (le_abs_self _) hmn
      _ = C1 * |C4| * |C2| * Ad3.LR.B.maj k N (1 / 2) 1 h := by ring

end GlobalTheory.CompanionTheory.DInt2
