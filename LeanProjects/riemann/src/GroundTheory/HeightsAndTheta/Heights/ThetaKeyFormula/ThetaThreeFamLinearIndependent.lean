import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.RigSymFormTauINontrivial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Real MeasureTheory intervalIntegral Matrix

noncomputable section

def lineCoeff (h : ℂ → ℂ) (k : ℤ) (y : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..1, h (x + y * I) * cexp (-2 * π * I * k * (x + y * I))

lemma lineCoeff_const (h : ℂ → ℂ) (hd : Differentiable ℂ h) (h1 : ∀ w, h (w + 1) = h w)
    (k : ℤ) (y₁ y₂ : ℝ) : lineCoeff h k y₁ = lineCoeff h k y₂ := by
  set F : ℂ → ℂ := fun w => h w * cexp (-2 * π * I * k * w) with hF
  have hFd : Differentiable ℂ F := hd.mul (by fun_prop)
  have hper : ∀ w, F (w + 1) = F w := by
    intro w
    simp only [hF, h1]
    congr 1
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨-k, by push_cast; ring⟩
  have := integral_boundary_rect_eq_zero_of_differentiableOn F ⟨0, y₁⟩ ⟨1, y₂⟩ hFd.differentiableOn
  simp only at this
  have hv : (∫ y : ℝ in y₁..y₂, F ((1 : ℝ) + y * I)) = ∫ y : ℝ in y₁..y₂, F ((0 : ℝ) + y * I) := by
    congr 1; funext y
    rw [show ((1 : ℝ) : ℂ) + y * I = ((0 : ℝ) + y * I) + 1 by push_cast; ring, hper]
  rw [hv, add_sub_cancel_right, sub_eq_zero] at this
  simpa [lineCoeff, hF] using this

lemma lineCoeff_shift (h : ℂ → ℂ) (n : ℕ) (C : ℂ)
    (h2 : ∀ w, h (w + I) = C * cexp (-2 * π * I * n * w) * h w) (k : ℤ) (y : ℝ) :
    lineCoeff h k (y + 1) = C * cexp (2 * π * k) * lineCoeff h (k + n) y := by
  unfold lineCoeff
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext x
  have e : (x : ℂ) + ((y + 1 : ℝ) : ℂ) * I = ((x : ℂ) + (y : ℂ) * I) + I := by push_cast; ring
  rw [e, h2]
  have : cexp (-2 * π * I * k * ((x + y * I) + I)) * cexp (-2 * π * I * n * (x + y * I)) =
      cexp (2 * π * k) * cexp (-2 * π * I * ((k + n : ℤ) : ℂ) * (x + y * I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
  calc C * cexp (-2 * π * I * n * (x + y * I)) * h (x + y * I) *
        cexp (-2 * π * I * k * ((x + y * I) + I))
      = C * (cexp (-2 * π * I * k * ((x + y * I) + I)) * cexp (-2 * π * I * n * (x + y * I))) *
          h (x + y * I) := by ring
    _ = _ := by rw [this]; ring

theorem quasiPeriodic_eq_zero (n : ℕ) (hn : 0 < n) (h : ℂ → ℂ) (hd : Differentiable ℂ h) (C : ℂ)
    (hC : C ≠ 0) (h1 : ∀ w, h (w + 1) = h w)
    (h2 : ∀ w, h (w + I) = C * cexp (-2 * π * I * n * w) * h w)
    (h0 : ∀ k : ℕ, k < n → ∫ x in (0 : ℝ)..1, h x * cexp (-2 * π * I * k * x) = 0) : h = 0 := by

  have hrec : ∀ k : ℤ, lineCoeff h k 0 = C * cexp (2 * π * k) * lineCoeff h (k + n) 0 := by
    intro k
    rw [lineCoeff_const h hd h1 k 0 (0 + 1), lineCoeff_shift h n C h2]
  have hne : ∀ k : ℤ, C * cexp (2 * π * k) ≠ 0 := fun k => mul_ne_zero hC (Complex.exp_ne_zero _)
  have base : ∀ r : ℕ, r < n → lineCoeff h r 0 = 0 := by
    intro r hr
    simpa [lineCoeff] using h0 r hr
  have hq : ∀ q : ℤ, ∀ r : ℕ, r < n → lineCoeff h (q * n + r) 0 = 0 := by
    intro q r hr
    induction q using Int.induction_on with
    | zero => simpa using base r hr
    | succ q ih =>
      have := hrec (q * n + r)
      rw [ih, show (q : ℤ) * n + r + n = (q + 1) * n + r by ring] at this
      exact (mul_eq_zero.mp this.symm).resolve_left (hne _)
    | pred q ih =>
      have := hrec ((-(q : ℤ) - 1) * n + r)
      rw [show (-(q : ℤ) - 1) * n + r + n = -(q : ℤ) * n + r by ring, ih, mul_zero] at this
      exact this
  have hall : ∀ (k : ℤ) (y : ℝ), lineCoeff h k y = 0 := by
    intro k y
    rw [lineCoeff_const h hd h1 k y 0]
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have hlt := Int.emod_lt_of_pos k hn'
    have hnn := Int.emod_nonneg k hn'.ne'
    have := hq (k / n) (k % n).toNat (by omega)
    rwa [Int.toNat_of_nonneg (Int.emod_nonneg k hn'.ne'), Int.ediv_mul_add_emod] at this

  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hint : ∀ m : ℤ, ∀ w, h (w + m) = h w := by
    intro m
    induction m using Int.induction_on with
    | zero => simp
    | succ m ih => intro w; push_cast at ih ⊢; rw [← add_assoc, h1, ih]
    | pred m ih =>
      intro w; push_cast at ih ⊢
      rw [← h1 (w + (-(m : ℂ) - 1)), show w + (-(m : ℂ) - 1) + 1 = w + -(m : ℂ) by ring, ih]
  have hline : ∀ (y x : ℝ), x ∈ Set.Ico (0 : ℝ) (0 + 1) → h (x + y * I) = 0 := by
    intro y x hx
    set g : ℝ → ℂ := fun x => h (x + y * I) with hg
    have hgc : Continuous g := hd.continuous.comp (by fun_prop)
    have hg01 : g 0 = g (0 + 1) := by
      simp only [hg]; push_cast
      rw [show (0 : ℂ) + 1 + y * I = (0 + y * I) + 1 by ring, h1]
    let f : C(AddCircle (1 : ℝ), ℂ) :=
      ⟨AddCircle.liftIco 1 0 g, AddCircle.liftIco_continuous hg01 hgc.continuousOn⟩
    have hcoef : ∀ k : ℤ, fourierCoeff f k = 0 := by
      intro k
      change fourierCoeff (AddCircle.liftIco 1 0 g) k = 0
      rw [fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral]
      have e : ∀ x : ℝ, fourier (-k) (x : AddCircle ((0 : ℝ) + 1 - 0)) • g x =
          cexp (-2 * π * k * y) * (h (x + y * I) * cexp (-2 * π * I * k * (x + y * I))) := by
        intro x
        rw [fourier_coe_apply, smul_eq_mul]
        have : cexp (2 * π * I * ((-k : ℤ) : ℂ) * x / ((0 + 1 - 0 : ℝ) : ℂ)) =
            cexp (-2 * π * k * y) * cexp (-2 * π * I * k * (x + y * I)) := by
          rw [← Complex.exp_add]; congr 1; push_cast
          linear_combination (2 * π * k * y) * I_sq
        rw [this]; simp only [hg]; ring
      simp_rw [e]
      rw [intervalIntegral.integral_const_mul]
      have := hall k y
      simp only [lineCoeff] at this
      simp only [zero_add, this, mul_zero, smul_zero]
    have hs := has_pointwise_sum_fourier_series_of_summable (f := f)
      (by rw [show fourierCoeff f = fun _ => 0 from funext hcoef]; exact summable_zero) (x : AddCircle (1 : ℝ))
    simp only [hcoef, zero_smul] at hs
    have h0f : f (x : AddCircle (1 : ℝ)) = g x := by
      change AddCircle.liftIco 1 0 g (x : AddCircle (1 : ℝ)) = g x
      exact AddCircle.liftIco_coe_apply hx
    change g x = 0
    rw [← h0f]
    exact (hasSum_zero.unique hs).symm
  funext w
  have hx : Int.fract w.re ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    rw [zero_add]; exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have := hline w.im (Int.fract w.re) hx
  rw [← hint ⌊w.re⌋] at this
  have hw : ((Int.fract w.re : ℝ) : ℂ) + w.im * I + (⌊w.re⌋ : ℂ) = w := by
    apply Complex.ext
    · simp [Int.fract_add_floor]
    · simp
  rw [hw] at this
  simpa using this

def thetaThree (ν : ℕ) (w : ℂ) : ℂ :=
  cexp (π * I * ν ^ 2 * I / 3 + 2 * π * I * ν * w) * jacobiTheta₂ (3 * w + ν * I) (3 * I)

lemma im_three_I_pos : 0 < (3 * I).im := by simp

lemma thetaThree_differentiable (ν : ℕ) : Differentiable ℂ (thetaThree ν) := by
  intro w
  have h1 : DifferentiableAt ℂ (fun w : ℂ => jacobiTheta₂ w (3 * I)) (3 * w + ν * I) :=
    differentiableAt_jacobiTheta₂_fst _ im_three_I_pos
  have h2 : DifferentiableAt ℂ (fun w : ℂ => 3 * w + ν * I) w := by fun_prop
  have h3 : DifferentiableAt ℂ ((fun w : ℂ => jacobiTheta₂ w (3 * I)) ∘ (fun w : ℂ => 3 * w + ν * I)) w :=
    DifferentiableAt.comp w h1 h2
  exact (by fun_prop : DifferentiableAt ℂ
    (fun w : ℂ => cexp (π * I * ν ^ 2 * I / 3 + 2 * π * I * ν * w)) w).mul h3

lemma thetaThree_add_one (ν : ℕ) (w : ℂ) : thetaThree ν (w + 1) = thetaThree ν w := by
  unfold thetaThree
  rw [show 3 * (w + 1) + ν * I = (3 * w + ν * I) + ((3 : ℤ) : ℂ) by push_cast; ring,
    jacobiTheta₂_add_int]
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  exact ⟨ν, by push_cast; ring⟩

lemma thetaThree_add_int_mul_I (ν : ℕ) (k : ℤ) (w : ℂ) :
    thetaThree ν (w + k * I) =
      cexp (-(3 * π * I * k ^ 2 * I) - 6 * π * I * k * w) * thetaThree ν w := by
  unfold thetaThree
  rw [show 3 * (w + k * I) + ν * I = (3 * w + ν * I) + k * (3 * I) by ring, jacobiTheta₂_add_int_mul]
  simp only [← mul_assoc, ← Complex.exp_add]
  congr 2; ring

lemma thetaThree_add_int (ν : ℕ) (m : ℤ) (w : ℂ) : thetaThree ν (w + m) = thetaThree ν w := by
  induction m using Int.induction_on generalizing w with
  | zero => simp
  | succ j ih => push_cast at ih ⊢; rw [← add_assoc, thetaThree_add_one, ih]
  | pred j ih =>
    push_cast at ih ⊢
    rw [← thetaThree_add_one ν (w + (-(j : ℂ) - 1)),
      show w + (-(j : ℂ) - 1) + 1 = w + -(j : ℂ) by ring, ih]

def zeta3 : ℂ := cexp (2 * π * I / 3)

lemma zeta_three_cube : zeta3 ^ 3 = 1 := by
  unfold zeta3
  rw [← Complex.exp_nat_mul, show ((3 : ℕ) : ℂ) * (2 * π * I / 3) = 2 * π * I by push_cast; ring,
    Complex.exp_two_pi_mul_I]

lemma one_add_zeta_three_add_sq : 1 + zeta3 + zeta3 ^ 2 = 0 := by
  have h := (Complex.isPrimitiveRoot_exp 3 (by norm_num)).geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h
  have e : cexp (2 * π * I / ((3 : ℕ) : ℂ)) = zeta3 := by unfold zeta3; push_cast; rfl
  rw [e] at h; exact h

lemma thetaThree_add_third (ν : ℕ) (w : ℂ) : thetaThree ν (w + 1 / 3) = zeta3 ^ ν * thetaThree ν w := by
  unfold thetaThree zeta3
  rw [show 3 * (w + 1 / 3) + ν * I = (3 * w + ν * I) + 1 by ring, jacobiTheta₂_add_left,
    ← Complex.exp_nat_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2; ring

lemma jacobiTheta₂_zero_three_I_ne : jacobiTheta₂ 0 (3 * I) ≠ 0 := by
  intro h
  have hb := norm_jacobiTheta_sub_one_le (τ := 3 * I) im_three_I_pos
  rw [jacobiTheta_eq_jacobiTheta₂, h] at hb
  simp only [zero_sub, norm_neg, norm_one] at hb
  have him : (3 * I).im = 3 := by simp
  rw [him] at hb
  have hπ : 3 < Real.exp (Real.pi * 3) := by
    have := Real.add_one_le_exp (Real.pi * 3)
    nlinarith [Real.pi_gt_three]
  have ht : Real.exp (-Real.pi * 3) < 1 / 3 := by
    rw [show -Real.pi * 3 = -(Real.pi * 3) by ring, Real.exp_neg,
      inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    simpa using hπ
  have htpos := Real.exp_pos (-Real.pi * 3)
  have h1 : 0 < 1 - Real.exp (-Real.pi * 3) := by linarith
  have : 2 / (1 - Real.exp (-Real.pi * 3)) * Real.exp (-Real.pi * 3) < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one h1]; linarith
  linarith

lemma thetaThree_ne_zero (ν : ℕ) : ∃ w, thetaThree ν w ≠ 0 := by
  refine ⟨-(ν * I) / 3, ?_⟩
  unfold thetaThree
  rw [show 3 * (-(ν * I) / 3) + ν * I = 0 by ring]
  exact mul_ne_zero (Complex.exp_ne_zero _) jacobiTheta₂_zero_three_I_ne

def thetaThreeSec (ν : ℕ) : (Fin 1 → ℂ) → ℂ := fun z => thetaThree ν (z 0)

theorem thetaThreeSec_mem (ν : ℕ) : thetaThreeSec ν ∈ thetaSec tauI (HalfChar.zero 1) 3 := by
  refine ⟨?_, fun v z => ?_, fun u z => ?_⟩
  · intro z
    exact (thetaThree_differentiable ν (z 0)).comp z ((differentiable_apply 0) z)
  · have : perFactor (HalfChar.zero 1) 3 v = 1 := by
      simp [perFactor, HalfChar.a, HalfChar.zero, dotProduct]
    rw [this, one_mul]
    simp only [thetaThreeSec, Pi.add_apply, intVec_one]
    induction (v 0) using Int.induction_on with
    | zero => simp
    | succ k ih => push_cast at ih ⊢; rw [← add_assoc, thetaThree_add_one, ih]
    | pred k ih =>
      push_cast at ih ⊢
      rw [← thetaThree_add_one ν (z 0 + (-(k : ℂ) - 1)),
        show z 0 + (-(k : ℂ) - 1) + 1 = z 0 + -(k : ℂ) by ring, ih]
  · simp only [thetaThreeSec, Pi.add_apply, autFactor, tauI]
    have hτ : ((I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) *ᵥ intVec u) 0 = (u 0 : ℂ) * I := by
      simp [Matrix.mulVec, dotProduct, intVec, mul_comm]
    rw [hτ, thetaThree_add_int_mul_I]
    congr 2
    simp [dotProduct, Matrix.mulVec, intVec, HalfChar.b, HalfChar.zero]
    ring_nf

def thetaThreeFam : Fin (2 + 1) → (Fin 1 → ℂ) → ℂ := fun ν => thetaThreeSec ν

lemma fn_eq_line (f : (Fin 1 → ℂ) → ℂ) (z : Fin 1 → ℂ) : f z = f (fun _ => z 0) := by
  congr 1; funext i; fin_cases i; rfl

theorem thetaThreeFam_linearIndependent : LinearIndependent ℂ thetaThreeFam := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hE : ∀ w : ℂ, c 0 * thetaThree 0 w + c 1 * thetaThree 1 w + c 2 * thetaThree 2 w = 0 := by
    intro w
    have := congrFun hc (fun _ => w)
    simpa [Fin.sum_univ_three, thetaThreeFam, thetaThreeSec] using this
  have key : ∀ w : ℂ, c 0 * thetaThree 0 w = 0 ∧ c 1 * thetaThree 1 w = 0 ∧
      c 2 * thetaThree 2 w = 0 := by
    intro w
    have e0 := hE w
    have e1 := hE (w + 1 / 3)
    have e2 := hE (w + 1 / 3 + 1 / 3)
    simp only [thetaThree_add_third] at e1 e2
    have hs := one_add_zeta_three_add_sq
    have hc3 := zeta_three_cube
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (1 / 3 : ℂ) * (e0 + e1 + e2) -
        (1 / 3 : ℂ) * (c 1 * thetaThree 1 w + c 2 * thetaThree 2 w) * hs -
        (1 / 3 : ℂ) * c 2 * thetaThree 2 w * zeta3 * hc3
    · linear_combination (1 / 3 : ℂ) * (e0 + zeta3 ^ 2 * e1 + zeta3 * e2) -
        (1 / 3 : ℂ) * (c 0 * thetaThree 0 w + c 2 * thetaThree 2 w) * hs -
        (1 / 3 : ℂ) * (2 * c 1 * thetaThree 1 w + c 2 * thetaThree 2 w * (zeta3 + zeta3 ^ 2)) * hc3
    · linear_combination (1 / 3 : ℂ) * (e0 + zeta3 * e1 + zeta3 ^ 2 * e2) -
        (1 / 3 : ℂ) * (c 0 * thetaThree 0 w + c 1 * thetaThree 1 w) * hs -
        (1 / 3 : ℂ) * (c 1 * thetaThree 1 w * zeta3 + c 2 * thetaThree 2 w * (zeta3 ^ 3 + 2)) * hc3
  intro i
  fin_cases i
  · obtain ⟨w, hw⟩ := thetaThree_ne_zero 0
    exact (mul_eq_zero.mp (key w).1).resolve_right hw
  · obtain ⟨w, hw⟩ := thetaThree_ne_zero 1
    exact (mul_eq_zero.mp (key w).2.1).resolve_right hw
  · obtain ⟨w, hw⟩ := thetaThree_ne_zero 2
    exact (mul_eq_zero.mp (key w).2.2).resolve_right hw

abbrev thetaThreeSpace : Submodule ℂ ((Fin 1 → ℂ) → ℂ) := thetaSec tauI (HalfChar.zero 1) 3

lemma line_continuous {f : (Fin 1 → ℂ) → ℂ} (hf : f ∈ thetaThreeSpace) (k : ℕ) :
    Continuous (fun x : ℝ => f (fun _ => (x : ℂ)) * cexp (-2 * π * I * k * x)) :=
  (hf.1.continuous.comp (continuous_pi fun _ => Complex.continuous_ofReal)).mul (by fun_prop)

def coeffMap : thetaThreeSpace →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun f k := ∫ x in (0 : ℝ)..1,
    (f : (Fin 1 → ℂ) → ℂ) (fun _ => (x : ℂ)) * cexp (-2 * π * I * (k : ℕ) * x)
  map_add' f h := by
    funext k
    simp only [Submodule.coe_add, Pi.add_apply, add_mul]
    exact intervalIntegral.integral_add
      ((line_continuous f.2 k).intervalIntegrable 0 1) ((line_continuous h.2 k).intervalIntegrable 0 1)
  map_smul' c f := by
    funext k
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact intervalIntegral.integral_const_mul _ _

theorem coeffMap_injective : Function.Injective coeffMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨f, hf⟩ h0
  obtain ⟨hd, hper, haut⟩ := id hf
  set F : ℂ → ℂ := fun w => f (fun _ => w) with hF
  have hFd : Differentiable ℂ F := hd.comp (differentiable_pi.2 fun _ => differentiable_id)
  have h1 : ∀ w, F (w + 1) = F w := by
    intro w
    have := hper (fun _ => 1) (fun _ => w)
    have hp : perFactor (HalfChar.zero 1) 3 (fun _ => 1) = 1 := by
      simp [perFactor, HalfChar.a, HalfChar.zero, dotProduct]
    rw [hp, one_mul] at this
    simp only [hF]
    convert this using 2
    funext i; simp [intVec]
  have h2 : ∀ w, F (w + I) = cexp (-(π * I * 3 * I)) * cexp (-2 * π * I * (3 : ℕ) * w) * F w := by
    intro w
    have := haut (fun _ => 1) (fun _ => w)
    simp only [hF]
    have hz : (fun _ : Fin 1 => w) + tauI.τ *ᵥ intVec (fun _ => 1) = fun _ => w + I := by
      funext i; fin_cases i; simp [tauI, Matrix.mulVec, dotProduct, intVec]
    rw [hz] at this
    rw [this, ← Complex.exp_add]
    congr 2
    simp [autFactor, tauI, Matrix.mulVec, dotProduct, intVec, HalfChar.b, HalfChar.zero]
    ring_nf
  have hzero : F = 0 := by
    refine quasiPeriodic_eq_zero 3 (by norm_num) F hFd _ (Complex.exp_ne_zero _) h1 h2 ?_
    intro k hk
    have := congrFun h0 ⟨k, hk⟩
    simpa [coeffMap, hF] using this
  apply Subtype.ext
  funext z
  show f z = 0
  rw [fn_eq_line f z]
  exact congrFun hzero (z 0)

theorem thetaThreeFam_span : Submodule.span ℂ (Set.range thetaThreeFam) = thetaThreeSpace := by
  have : Module.Finite ℂ thetaThreeSpace := Module.Finite.of_injective coeffMap coeffMap_injective
  have hle : Module.finrank ℂ thetaThreeSpace ≤ 3 := by
    simpa using LinearMap.finrank_le_finrank_of_injective coeffMap_injective
  let y : Fin (2 + 1) → thetaThreeSpace := fun ν => ⟨thetaThreeFam ν, thetaThreeSec_mem ν⟩
  have hy : LinearIndependent ℂ y :=
    LinearIndependent.of_comp thetaThreeSpace.subtype thetaThreeFam_linearIndependent
  have hcard : Fintype.card (Fin (2 + 1)) = Module.finrank ℂ thetaThreeSpace :=
    le_antisymm hy.fintype_card_le_finrank (by simpa using hle)
  have hspan := hy.span_eq_top_of_card_eq_finrank' hcard
  have hr : Set.range thetaThreeFam = thetaThreeSpace.subtype '' Set.range y := by
    rw [← Set.range_comp]; rfl
  rw [hr, Submodule.span_image, hspan, Submodule.map_subtype_top]

theorem thetaThree_zero_finite :
    ∃ W : Finset ℂ, ∀ w, thetaThree 0 w = 0 → ∃ w' ∈ W, ∃ m k : ℤ, w = w' + k * I + m := by
  set S : Set ℂ := {w | w ∈ Metric.closedBall (0 : ℂ) 2 ∧ thetaThree 0 w = 0} with hS
  have hSfin : S.Finite := by
    by_contra hinf
    obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
      (isCompact_closedBall (0 : ℂ) 2) (fun w hw => hw.1)
    rw [accPt_iff_frequently_nhdsNE] at hx
    have han : AnalyticOnNhd ℂ (thetaThree 0) Set.univ :=
      fun z _ => (thetaThree_differentiable 0).analyticAt z
    have := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (Set.mem_univ x) (hx.mono fun w hw => hw.2)
    obtain ⟨w, hw⟩ := thetaThree_ne_zero 0
    exact hw (this (Set.mem_univ w))
  refine ⟨hSfin.toFinset, fun w hw => ?_⟩
  set m := ⌊w.re⌋ with hm
  set k := ⌊w.im⌋ with hk
  set w' : ℂ := w - k * I - m with hw'
  have hshift : thetaThree 0 w = cexp (-(3 * π * I * k ^ 2 * I) - 6 * π * I * k * (w' + m)) *
      thetaThree 0 w' := by
    have e : w = (w' + m) + k * I := by rw [hw']; ring
    rw [e, thetaThree_add_int_mul_I, thetaThree_add_int]
  have hz' : thetaThree 0 w' = 0 := by
    rw [hshift] at hw
    exact (mul_eq_zero.mp hw).resolve_left (Complex.exp_ne_zero _)
  have hre : w'.re = Int.fract w.re := by rw [← Int.self_sub_floor]; simp [hw', hm]
  have him : w'.im = Int.fract w.im := by rw [← Int.self_sub_floor]; simp [hw', hk]
  have hball : w' ∈ Metric.closedBall (0 : ℂ) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖w'‖ ≤ |w'.re| + |w'.im| := Complex.norm_le_abs_re_add_abs_im w'
      _ ≤ 1 + 1 := by
        rw [hre, him]
        gcongr
        · rw [abs_of_nonneg (Int.fract_nonneg _)]; exact (Int.fract_lt_one _).le
        · rw [abs_of_nonneg (Int.fract_nonneg _)]; exact (Int.fract_lt_one _).le
      _ = 2 := by norm_num
  refine ⟨w', hSfin.mem_toFinset.mpr ⟨hball, hz'⟩, m, k, ?_⟩
  rw [hw']; ring

end

end GroundTheory.Heights₂.Heights.KeyFormula
