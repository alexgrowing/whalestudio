import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff

noncomputable section

open MeasureTheory Matrix Set
open Ad3.K Ad3.K.LC Ad3.K.LC.C

namespace GlobalTheory.CompanionTheory.GodementFE

theorem e_ne (a : ℂˣ) : ((a : ℂ) / (‖(a : ℂ)‖ : ℂ)) ≠ 0 := by
  have h1 : (a : ℂ) ≠ 0 := a.ne_zero
  have h2 : ((‖(a : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 h1)
  exact div_ne_zero h1 h2

theorem r_ne (a : ℂˣ) : (((‖(a : ℂ)‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by
  have h1 : (a : ℂ) ≠ 0 := a.ne_zero
  have h2 : ‖(a : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 h1
  exact_mod_cast pow_ne_zero 2 h2

theorem ph_mul (n : ℤ) (a b : ℂ) : ph n (a * b) = ph n a * ph n b := by
  unfold ph
  rw [← mul_zpow]
  congr 1
  rw [norm_mul]
  push_cast
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have h1 : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 ha)
  have h2 : ((‖b‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hb)
  field_simp

theorem chC_add (p q : ℤ) (s s' : ℂ) (a : ℂˣ) :
    chC p s a * chC q s' a = chC (p + q) (s + s') a := by
  unfold chC
  rw [zpow_add₀ (e_ne a), Complex.cpow_add _ _ (r_ne a)]
  ring

theorem chC_mul (p : ℤ) (s : ℂ) (a b : ℂˣ) : chC p s (a * b) = chC p s a * chC p s b := by
  unfold chC
  have h1 : ((a * b : ℂˣ) : ℂ) = (a : ℂ) * b := rfl
  have h2 : ((a : ℂ) * b) / (‖(a : ℂ) * b‖ : ℂ) = ((a : ℂ) / ‖(a : ℂ)‖) * ((b : ℂ) / ‖(b : ℂ)‖) := by
    have := e_ne a
    have := e_ne b
    rw [norm_mul]
    push_cast
    rw [mul_div_mul_comm]
  have h3 : (((‖(a : ℂ) * b‖ ^ 2 : ℝ)) : ℂ) ^ s =
      (((‖(a : ℂ)‖ ^ 2 : ℝ)) : ℂ) ^ s * (((‖(b : ℂ)‖ ^ 2 : ℝ)) : ℂ) ^ s := by
    rw [norm_mul, mul_pow, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  rw [h1, h2, h3, mul_zpow]
  ring

theorem chC_zero (a : ℂˣ) : chC 0 0 a = 1 := by
  simp [chC]

theorem chC_one (p : ℤ) (s : ℂ) : chC p s 1 = 1 := by
  simp [chC]

theorem chC_ne (p : ℤ) (s : ℂ) (a : ℂˣ) : chC p s a ≠ 0 := by
  unfold chC
  exact mul_ne_zero (zpow_ne_zero _ (e_ne a)) (by simp [Complex.cpow_eq_zero_iff, r_ne a])

theorem chC_inv (p : ℤ) (s : ℂ) (a : ℂˣ) : chC p s a⁻¹ = chC (-p) (-s) a := by
  have h1 : chC p s a⁻¹ * chC p s a = 1 := by
    rw [← chC_mul, inv_mul_cancel, chC_one]
  have h2 : chC (-p) (-s) a * chC p s a = 1 := by
    rw [chC_add]
    simp [chC_zero]
  exact mul_right_cancel₀ (chC_ne p s a) (h1.trans h2.symm)

theorem chC_half (p : ℤ) (a : ℂˣ) : chC p (1 / 2) a = ph p a * ((‖(a : ℂ)‖ : ℝ) : ℂ) := by
  unfold chC ph
  congr 1
  have h0 : (0 : ℝ) ≤ ‖(a : ℂ)‖ := norm_nonneg _
  have e : (((‖(a : ℂ)‖ ^ 2 : ℝ)) : ℂ) ^ (1 / 2 : ℂ) = (((‖(a : ℂ)‖ ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    norm_num
  rw [e, ← Real.sqrt_eq_rpow, Real.sqrt_sq h0]

theorem chC_zero_ph (p : ℤ) (a : ℂˣ) : chC p 0 a = ph p a := by
  simp [chC, ph]

theorem chC_neg_one (p : ℤ) (s : ℂ) : chC p s (-1) = (-1) ^ p := by
  simp [chC]

theorem norm_chC (p : ℤ) (s : ℂ) (a : ℂˣ) : ‖chC p s a‖ = ‖(a : ℂ)‖ ^ (2 * s.re) := by
  have hp : 0 < ‖(a : ℂ)‖ := norm_pos_iff.2 a.ne_zero
  have h1 : ‖((a : ℂ) / (‖(a : ℂ)‖ : ℂ))‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self hp.ne']
  unfold chC
  rw [norm_mul, norm_zpow, h1, _root_.one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  norm_num

theorem measurable_chC (p : ℤ) (s : ℂ) : Measurable (chC p s) := by
  have hv : Measurable (Units.val : ℂˣ → ℂ) := val_measEmb.measurable
  unfold chC
  fun_prop

theorem wt_int (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    Integrable (fun a : ℂˣ => ‖(a : ℂ)‖ ^ (2 * σ) * dd a) mulC := by
  set F : ℂ → ℂ := fun z => ((‖z‖ ^ (2 * σ) * dd z : ℝ) : ℂ) with hF
  have h := (integrable_mulC_iff F).2 (by
    refine (wt_vol σ h0 h1).ofReal.congr ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with z hz
    have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hF]
    rw [← Complex.ofReal_mul]
    refine congrArg _ ?_
    show ‖z‖ ^ (2 * σ - 2) * dd z = (‖z‖ ^ 2)⁻¹ * (‖z‖ ^ (2 * σ) * dd z)
    rw [Real.rpow_sub hzp, Real.rpow_two]
    ring)
  refine h.norm.congr (Filter.Eventually.of_forall fun a => ?_)
  simp only [hF]
  rw [Complex.norm_real, Real.norm_of_nonneg]
  have := dd_pos (a : ℂ)
  positivity

theorem prod_int (G : ℂ → ℂ → ℂ) (hG : Measurable fun p : ℂ × ℂ => G p.1 p.2) (C : ℝ)
    (hb : ∀ x ξ, ‖G x ξ‖ ≤ C * (dd x * dd ξ)) (p q : ℤ) (s s' : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (h0' : 0 < s'.re) (h1' : s'.re < 1) :
    Integrable (fun z : ℂˣ × ℂˣ => G z.1 z.2 * chC p s z.1 * chC q s' z.2) (mulC.prod mulC) := by
  have hv : Measurable (Units.val : ℂˣ → ℂ) := val_measEmb.measurable
  have hW := ((wt_int s.re h0 h1).mul_prod (wt_int s'.re h0' h1')).const_mul C
  refine hW.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · have m1 : Measurable fun z : ℂˣ × ℂˣ => G z.1 z.2 :=
      hG.comp ((hv.comp measurable_fst).prodMk (hv.comp measurable_snd))
    have m2 : Measurable fun z : ℂˣ × ℂˣ => chC p s z.1 := (measurable_chC p s).comp measurable_fst
    have m3 : Measurable fun z : ℂˣ × ℂˣ => chC q s' z.2 := (measurable_chC q s').comp measurable_snd
    exact ((m1.mul m2).mul m3).aestronglyMeasurable
  · rw [norm_mul, norm_mul, norm_chC, norm_chC]
    have h := hb z.1 z.2
    have a1 : 0 ≤ ‖((z.1 : ℂˣ) : ℂ)‖ ^ (2 * s.re) := by positivity
    have a2 : 0 ≤ ‖((z.2 : ℂˣ) : ℂ)‖ ^ (2 * s'.re) := by positivity
    calc _ ≤ C * (dd z.1 * dd z.2) * ‖((z.1 : ℂˣ) : ℂ)‖ ^ (2 * s.re) * ‖((z.2 : ℂˣ) : ℂ)‖ ^ (2 * s'.re) := by gcongr
      _ = _ := by ring

theorem shear (H : ℂˣ × ℂˣ → ℂ) (hH : Integrable H (mulC.prod mulC)) :
    ∫ a, ∫ t, H (t * a, t⁻¹) ∂mulC ∂mulC = ∫ x, ∫ ξ, H (x, ξ) ∂mulC ∂mulC := by
  have p1 : MeasurePreserving (fun z : ℂˣ × ℂˣ => (z.2, z.1)) (mulC.prod mulC) (mulC.prod mulC) :=
    Measure.measurePreserving_swap
  have p2 := measurePreserving_prod_mul (mulC) (mulC)
  have p4 : MeasurePreserving (fun z : ℂˣ × ℂˣ => (z.1, z.2⁻¹)) (mulC.prod mulC) (mulC.prod mulC) :=
    (MeasurePreserving.id mulC).prod mp_inv
  have hT : MeasurePreserving (fun z : ℂˣ × ℂˣ => (z.2 * z.1, z.2⁻¹)) (mulC.prod mulC) (mulC.prod mulC) :=
    ((p4.comp p1).comp p2).comp p1
  have hI : Integrable (fun z : ℂˣ × ℂˣ => H (z.2 * z.1, z.2⁻¹)) (mulC.prod mulC) :=
    hT.integrable_comp hH.aestronglyMeasurable |>.2 hH
  rw [← integral_prod _ hH, ← integral_prod (fun z : ℂˣ × ℂˣ => H (z.2 * z.1, z.2⁻¹)) hI]
  conv_rhs => rw [← hT.map_eq]
  rw [integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hH.aestronglyMeasurable)]

theorem whittaker_translate (k : ℕ) (f : (Fin 2 → ℂ) → ℂ) (M g : Matrix (Fin 2) (Fin 2) ℂ) :
    W2 k f (M * g) = ph (2 * (k : ℤ) - 2) g.det * ((‖g.det‖ : ℝ) : ℂ) *
      W2 k (fun v => f (Matrix.vecMul v g)) M := by
  unfold W2
  rw [Matrix.det_mul, ph_mul, norm_mul]
  simp only [Matrix.vecMul_vecMul]
  push_cast
  ring

theorem det_diagonal_alt (a : ℂ) : (d2 a).det = a := by
  simp [d2, Matrix.det_fin_two_of]

theorem det_weyl_element : w2.det = 1 := by
  simp [w2, Matrix.det_fin_two_of]

theorem vecMul_diagonal_alt (a t y : ℂ) : Matrix.vecMul ![t, t * y] (d2 a) = ![t * a, t * y] := by
  ext i
  fin_cases i <;> simp [d2, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem whittaker_diagonal (k : ℕ) (f : (Fin 2 → ℂ) → ℂ) (a : ℂˣ) :
    W2 k f (d2 a) = ph (2 * (k : ℤ) - 2) a * ((‖(a : ℂ)‖ : ℝ) : ℂ) *
      ∫ t : ℂˣ, ph (4 * (k : ℤ) - 4) t * sF f (t * a) (t⁻¹ : ℂˣ) ∂mulC := by
  unfold W2
  rw [det_diagonal_alt]
  congr 1
  have e := integral_mulC (fun z : ℂ => ph (4 * (k : ℤ) - 4) z * sF f (z * a) z⁻¹)
  have e' : ∫ t : ℂˣ, ph (4 * (k : ℤ) - 4) t * sF f (t * a) (t⁻¹ : ℂˣ) ∂mulC =
      ∫ t : ℂˣ, ph (4 * (k : ℤ) - 4) t * sF f (t * a) (t : ℂ)⁻¹ ∂mulC := by
    simp only [Units.val_inv_eq_inv_val]
  rw [e', e]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with t ht
  have ht0 : t ≠ 0 := ht
  simp only [vecMul_diagonal_alt]
  have h := integral_comp_mul t ht0 (fun u : ℂ => f ![t * a, u] * psiC (-(u * t⁻¹)))
  have e2 : ∀ y : ℂ, t * y * t⁻¹ = y := fun y => by field_simp
  simp only [e2] at h
  rw [h, sF]
  ring

theorem fC_eq (h : ℂ → ℂ) (w : ℂ) : fC h w = 2 * ∫ u : ℂ, h u * psiC (-(u * (-w))) := by
  unfold fC volC
  rw [integral_smul_measure]
  simp

theorem schw_bound' (f : SchwartzMap (Fin 2 → ℂ) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x u : ℂ, ‖f ![x, u]‖ ≤ C * (dd x * dd u) := by
  obtain ⟨C, hC, hb⟩ := schw_bound f
  refine ⟨C, hC, fun x u => (hb x u).trans ?_⟩
  have h1 : dd u ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [norm_nonneg u])
  have hu := dd_pos u
  have hx := dd_pos x
  have : dd u ^ 2 ≤ dd u := by nlinarith
  gcongr

theorem neg_one_sq (m : ℤ) : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by
  rw [← mul_zpow]
  simp

theorem tate_slice (hT : TateFunctionalEquationComplex) (f : SchwartzMap (Fin 2 → ℂ) ℂ) (x : ℂ) (m : ℤ) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    ∫ ξ : ℂˣ, sF f x ξ * chC m s ξ ∂mulC =
      (1 / 2) * (-1) ^ m * gC (-m) (1 - s) * ∫ u : ℂˣ, f ![x, u] * chC (-m) (1 - s) u ∂mulC := by
  set h : ℂ → ℂ := fun u => f ![x, u] with hh
  obtain ⟨C, hC, hb⟩ := schw_bound' f
  obtain ⟨C', hC', hb'⟩ := sF_decay f
  have hre : (1 - s).re = 1 - s.re := by simp
  have h0' : 0 < (1 - s).re := by rw [hre]; linarith
  have h1' : (1 - s).re < 1 := by rw [hre]; linarith
  have hfC : ∀ w, fC h w = 2 * sF f x (-w) := fun w => fC_eq h w
  have hxd := dd_pos x
  have i2 : Integrable (fun w => h w * ((‖w‖ ^ (2 * ((1 - s).re - 1)) : ℝ) : ℂ)) := by
    have hW := (wt_vol (1 - s).re h0' h1').const_mul (C * dd x)
    refine hW.mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
    · refine ((continuous_slice f x).measurable.mul ?_).aestronglyMeasurable
      fun_prop
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        show 2 * ((1 - s).re - 1) = 2 * (1 - s).re - 2 by ring]
      have := hb x w
      have hp : 0 ≤ ‖w‖ ^ (2 * (1 - s).re - 2) := by positivity
      calc _ ≤ C * (dd x * dd w) * ‖w‖ ^ (2 * (1 - s).re - 2) := by gcongr
        _ = _ := by ring
  have i3 : Integrable (fun r => fC h r * ((‖r‖ ^ (-2 * (1 - s).re) : ℝ) : ℂ)) := by
    have hW := (wt_vol s.re h0 h1).const_mul (2 * (C' * dd x))
    refine hW.mono' ?_ (Filter.Eventually.of_forall fun r => ?_)
    · have m1 : Measurable fun r : ℂ => sF f x (-r) :=
        (measurable_sF f).comp (measurable_const.prodMk measurable_neg)
      have m2 : Measurable fun r : ℂ => fC h r := by
        simp only [hfC]
        exact m1.const_mul 2
      refine (m2.mul ?_).aestronglyMeasurable
      fun_prop
    · rw [hfC, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), hre,
        show -2 * (1 - s.re) = 2 * s.re - 2 by ring]
      have := hb' x (-r)
      have e : dd (-r) = dd r := by simp [dd]
      rw [e] at this
      have hp : 0 ≤ ‖r‖ ^ (2 * s.re - 2) := by positivity
      have n2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [n2]
      calc _ ≤ 2 * (C' * (dd x * dd r)) * ‖r‖ ^ (2 * s.re - 2) := by gcongr
        _ = _ := by ring
  have T := hT h (-m) (1 - s) h0' h1' (slice_int f x) i2 i3
  rw [neg_neg, sub_sub_cancel] at T
  unfold z1 at T
  set X : ℂ := ∫ ξ : ℂˣ, sF f x ξ * chC m s ξ ∂mulC with hX
  have A : ∫ a : ℂˣ, fC h a * chC m s a ∂mulC = 2 * (-1) ^ m * X := by
    have hinv := integral_mul_left_eq_self (μ := mulC) (fun a : ℂˣ => sF f x a * chC m s a) (-1 : ℂˣ)
    rw [hX, ← hinv, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only
    rw [hfC, chC_mul, chC_neg_one]
    have e : (((-1 : ℂˣ) * a : ℂˣ) : ℂ) = -(a : ℂ) := by simp
    rw [e]
    linear_combination (-(2 * sF f x (-(a : ℂ)) * chC m s a)) * neg_one_sq m
  rw [A] at T
  have hZ : ∫ u : ℂˣ, f ![x, u] * chC (-m) (1 - s) u ∂mulC = ∫ a : ℂˣ, h a * chC (-m) (1 - s) a ∂mulC := rfl
  rw [hZ]
  linear_combination ((1 / 2 : ℂ) * (-1) ^ m) * T - X * neg_one_sq m

theorem chi_id (p n : ℤ) (s : ℂ) (a t : ℂˣ) :
    ph p a * ((‖(a : ℂ)‖ : ℝ) : ℂ) * chC n (s - 1 / 2) a * ph (2 * p) t =
      chC (n + p) s (t * a) * chC (n - p) s t⁻¹ := by
  rw [← chC_half, chC_add, chC_mul, chC_inv, ← chC_zero_ph]
  have e : chC (n + p) s t * chC (n + p) s a * chC (-(n - p)) (-s) t =
      (chC (n + p) s t * chC (-(n - p)) (-s) t) * chC (n + p) s a := by ring
  rw [e, chC_add, mul_comm]
  congr 2
  · ring
  · ring
  · ring
  · ring

theorem key (hT : TateFunctionalEquationComplex) (k : ℕ) (f : SchwartzMap (Fin 2 → ℂ) ℂ) (n : ℤ) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    ∫ a : ℂˣ, W2 k f (d2 a) * chC n (s - 1 / 2) a ∂mulC =
      (1 / 2) * (-1) ^ (n - (2 * (k : ℤ) - 2)) * gC (-(n - (2 * (k : ℤ) - 2))) (1 - s) *
        ∫ x : ℂˣ, chC (n + (2 * (k : ℤ) - 2)) s x *
          ∫ u : ℂˣ, f ![(x : ℂ), (u : ℂ)] * chC (-(n - (2 * (k : ℤ) - 2))) (1 - s) u ∂mulC ∂mulC := by
  set p : ℤ := 2 * (k : ℤ) - 2 with hp
  obtain ⟨C, -, hb⟩ := sF_decay f
  set H : ℂˣ × ℂˣ → ℂ := fun z => sF f z.1 z.2 * chC (n + p) s z.1 * chC (n - p) s z.2 with hH
  have hI : Integrable H (mulC.prod mulC) :=
    prod_int (sF f) (measurable_sF f) C hb (n + p) (n - p) s s h0 h1 h0 h1
  have s1 : ∀ a : ℂˣ, W2 k f (d2 a) * chC n (s - 1 / 2) a = ∫ t, H (t * a, t⁻¹) ∂mulC := by
    intro a
    rw [whittaker_diagonal, mul_right_comm, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hH]
    have e := chi_id p n s a t
    rw [show (4 * (k : ℤ) - 4) = 2 * p by rw [hp]; ring]
    simp only [Units.val_mul] at e ⊢
    linear_combination (sF f ((t : ℂ) * a) ((t⁻¹ : ℂˣ) : ℂ)) * e
  simp only [s1]
  rw [shear H hI, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hH]
  have e : ∀ ξ : ℂˣ, sF f x ξ * chC (n + p) s x * chC (n - p) s ξ =
      chC (n + p) s x * (sF f x ξ * chC (n - p) s ξ) := fun ξ => by ring
  simp only [e]
  rw [integral_const_mul, tate_slice hT f x (n - p) s h0 h1]
  ring

theorem gC_neg (m : ℤ) (s : ℂ) : gC (-m) s = gC m s := by
  simp [gC, Int.natAbs_neg]

theorem gam_ne {z : ℂ} (hz : 0 < z.re) : Complex.Gammaℂ z ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hz)
  rw [Ne, Complex.cpow_eq_zero_iff]
  simp [Real.pi_ne_zero]

theorem gC_refl (m : ℤ) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    (-1 : ℂ) ^ m * (gC m s * gC m (1 - s)) = 1 := by
  set A : ℕ := m.natAbs with hA
  have hA0 : (0 : ℝ) ≤ (A : ℝ) / 2 := by positivity
  have g1 : Complex.Gammaℂ (s + (A : ℂ) / 2) ≠ 0 :=
    gam_ne (by
      have : (s + (A : ℂ) / 2).re = s.re + (A : ℝ) / 2 := by simp
      rw [this]
      linarith)
  have g2 : Complex.Gammaℂ (1 - s + (A : ℂ) / 2) ≠ 0 :=
    gam_ne (by
      have : (1 - s + (A : ℂ) / 2).re = 1 - s.re + (A : ℝ) / 2 := by simp
      rw [this]
      linarith)
  have hprod : gC m s * gC m (1 - s) = (-1 : ℂ) ^ A := by
    unfold gC
    rw [← hA, sub_sub_cancel]
    have : ((-Complex.I) ^ A) * ((-Complex.I) ^ A) = (-1 : ℂ) ^ A := by
      rw [← mul_pow]
      simp
    rw [← this]
    generalize Complex.Gammaℂ (1 - s + (A : ℂ) / 2) = G1 at g2 ⊢
    generalize Complex.Gammaℂ (s + (A : ℂ) / 2) = G2 at g1 ⊢
    field_simp
  rw [hprod]
  obtain ⟨q, hq | hq⟩ := Int.eq_nat_or_neg m
  · have : A = q := by rw [hA, hq]; simp
    rw [this, hq, zpow_natCast, ← mul_pow]
    simp
  · have : A = q := by rw [hA, hq]; simp
    rw [this, hq, _root_.zpow_neg, zpow_natCast, ← inv_pow, ← mul_pow]
    simp [← mul_pow]

theorem exists_translate (f : SchwartzMap (Fin 2 → ℂ) ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0) :
    ∃ f1 : SchwartzMap (Fin 2 → ℂ) ℂ, ∀ v, f1 v = f (Matrix.vecMul v g) := by
  have hu : IsUnit g.det := isUnit_iff_ne_zero.2 hg
  let e : (Fin 2 → ℂ) ≃ₗ[ℝ] (Fin 2 → ℂ) :=
    { toFun := fun v => Matrix.vecMul v g
      map_add' := fun a b => Matrix.add_vecMul g a b
      map_smul' := fun c a => Matrix.smul_vecMul c a g
      invFun := fun v => Matrix.vecMul v g⁻¹
      left_inv := fun v => by
        simp [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv g hu]
      right_inv := fun v => by
        simp [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul g hu] }
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.toContinuousLinearEquiv f, fun v => rfl⟩

theorem vecMul_weyl_element (x u : ℂ) : Matrix.vecMul ![x, u] w2 = ![-u, x] := by
  ext i
  fin_cases i <;> simp [w2, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem swap_I (f : SchwartzMap (Fin 2 → ℂ) ℂ) (q r : ℤ) (s s' : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (h0' : 0 < s'.re) (h1' : s'.re < 1) :
    ∫ x : ℂˣ, chC q s' x * ∫ u : ℂˣ, f ![-(u : ℂ), (x : ℂ)] * chC r s u ∂mulC ∂mulC =
      (-1) ^ r * ∫ x : ℂˣ, chC r s x * ∫ u : ℂˣ, f ![(x : ℂ), (u : ℂ)] * chC q s' u ∂mulC ∂mulC := by
  obtain ⟨C, -, hb⟩ := schw_bound' f
  have hm : Measurable fun p : ℂ × ℂ => f ![p.1, p.2] := (f.continuous.comp continuous_vec).measurable
  have hI := prod_int (fun x u => f ![x, u]) hm C hb r q s s' h0 h1 h0' h1'
  have inner : ∀ x : ℂˣ, ∫ u : ℂˣ, f ![-(u : ℂ), (x : ℂ)] * chC r s u ∂mulC =
      (-1) ^ r * ∫ u : ℂˣ, f ![(u : ℂ), (x : ℂ)] * chC r s u ∂mulC := by
    intro x
    have hinv := integral_mul_left_eq_self (μ := mulC)
      (fun u : ℂˣ => f ![(u : ℂ), (x : ℂ)] * chC r s ((-1 : ℂˣ) * u)) (-1 : ℂˣ)
    have e1 : ∀ u : ℂˣ, f ![(((-1 : ℂˣ) * u : ℂˣ) : ℂ), (x : ℂ)] * chC r s ((-1 : ℂˣ) * ((-1 : ℂˣ) * u)) =
        f ![-(u : ℂ), (x : ℂ)] * chC r s u := by
      intro u
      have e : (((-1 : ℂˣ) * u : ℂˣ) : ℂ) = -(u : ℂ) := by simp
      rw [e]
      simp
    have e2 : ∀ u : ℂˣ, f ![(u : ℂ), (x : ℂ)] * chC r s ((-1 : ℂˣ) * u) =
        (-1) ^ r * (f ![(u : ℂ), (x : ℂ)] * chC r s u) := by
      intro u
      rw [chC_mul, chC_neg_one]
      ring
    simp only [e1, e2] at hinv
    rw [hinv, integral_const_mul]
  simp only [inner]
  rw [← integral_const_mul]
  have hsw := integral_integral_swap (μ := mulC) (ν := mulC)
    (f := fun u x : ℂˣ => f ![(u : ℂ), (x : ℂ)] * chC r s u * chC q s' x) hI
  have l : ∀ x : ℂˣ, chC q s' x * ((-1) ^ r * ∫ u : ℂˣ, f ![(u : ℂ), (x : ℂ)] * chC r s u ∂mulC) =
      (-1) ^ r * ∫ u : ℂˣ, f ![(u : ℂ), (x : ℂ)] * chC r s u * chC q s' x ∂mulC := by
    intro x
    rw [integral_mul_const]
    ring
  have r' : ∀ x : ℂˣ, chC r s x * ∫ u : ℂˣ, f ![(x : ℂ), (u : ℂ)] * chC q s' u ∂mulC =
      ∫ u : ℂˣ, f ![(x : ℂ), (u : ℂ)] * chC r s x * chC q s' u ∂mulC := by
    intro x
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    ring
  simp only [l, r']
  rw [integral_const_mul, integral_const_mul, ← hsw]

theorem main : TateFunctionalEquationComplex → FunctionalEquationGL2GL1Complex := by
  intro hT k hk f n s g hg h0 h1
  have hre : (1 - s).re = 1 - s.re := by simp
  have h0' : 0 < (1 - s).re := by rw [hre]; linarith
  have h1' : (1 - s).re < 1 := by rw [hre]; linarith
  obtain ⟨f1, hf1⟩ := exists_translate f g hg
  obtain ⟨f2, hf2⟩ := exists_translate f1 w2 (by rw [det_weyl_element]; exact one_ne_zero)
  have hf1' : (fun v => f (Matrix.vecMul v g)) = ⇑f1 := funext fun v => (hf1 v).symm
  have hf2' : (fun v => f1 (Matrix.vecMul v w2)) = ⇑f2 := funext fun v => (hf2 v).symm
  set c : ℂ := ph (2 * (k : ℤ) - 2) g.det * ((‖g.det‖ : ℝ) : ℂ) with hc
  set p : ℤ := 2 * (k : ℤ) - 2 with hp
  have hph1 : ph p 1 = 1 := by simp [ph]
  have z1e : z2 k n s f g = c * ∫ a : ℂˣ, W2 k f1 (d2 a) * chC n (s - 1 / 2) a ∂mulC := by
    unfold z2
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only
    rw [whittaker_translate, hf1', ← hp, ← hc]
    ring
  have z2e : z2' k n s f g = c * ∫ a : ℂˣ, W2 k f2 (d2 a) * chC (-n) ((1 - s) - 1 / 2) a ∂mulC := by
    unfold z2'
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only
    rw [whittaker_translate, hf1', whittaker_translate, hf2', det_weyl_element, ← hp, ← hc, hph1,
      show (1 - s - 1 / 2 : ℂ) = 1 / 2 - s by ring]
    simp
    ring
  have K1 := key hT k f1 n s h0 h1
  have K2 := key hT k f2 (-n) (1 - s) h0' h1'
  rw [← hp] at K1 K2
  have e1 : -n - p = -(n + p) := by ring
  have e2 : -n + p = -(n - p) := by ring
  rw [e1, e2, neg_neg, sub_sub_cancel] at K2
  simp only [hf2, vecMul_weyl_element] at K2
  rw [swap_I f1 (-(n - p)) (n + p) s (1 - s) h0 h1 h0' h1'] at K2
  rw [gC_neg] at K1
  have G := gC_refl (n - p) s h0 h1
  have hN : ((-1 : ℂ) ^ (-(n + p))) * (-1) ^ (n + p) = 1 := by
    rw [_root_.zpow_neg]
    exact inv_mul_cancel₀ (zpow_ne_zero _ (by norm_num))
  have hcast : 2 * ((k - 1 : ℕ) : ℤ) = p := by
    rw [hp]
    omega
  rw [z1e, z2e, K1, K2, g2, hcast]
  generalize (∫ x : ℂˣ, chC (n + p) s x *
    ∫ u : ℂˣ, f1 ![(x : ℂ), (u : ℂ)] * chC (-(n - p)) (1 - s) u ∂mulC ∂mulC) = Iv
  linear_combination (c * (1 / 2) * gC (n + p) s * Iv) * hN - (c * (1 / 2) * gC (n + p) s * Iv) * G

end GlobalTheory.CompanionTheory.GodementFE
