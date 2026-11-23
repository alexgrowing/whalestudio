import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

open MeasureTheory
open scoped ComplexConjugate FourierTransform

section Decay

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def diffFun (f : SchwartzMap V ℂ) (y : V) : V → ℂ := fun x => f (x + y) * conj (f x)

theorem contDiff_translate (f : SchwartzMap V ℂ) (y : V) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => f (x + y)) :=
  (f.smooth ⊤).comp (contDiff_id.add contDiff_const)

theorem contDiff_conj (f : SchwartzMap V ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => conj (f x)) :=
  Complex.conjCLE.contDiff.comp (f.smooth ⊤)

theorem contDiff_diffFun (f : SchwartzMap V ℂ) (y : V) :
    ContDiff ℝ (⊤ : ℕ∞) (diffFun f y) :=
  (contDiff_translate f y).mul (contDiff_conj f)

theorem norm_iteratedFDeriv_conj (f : SchwartzMap V ℂ) (i : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ i (fun x => conj (f x)) x‖ = ‖iteratedFDeriv ℝ i f x‖ :=
  Complex.conjLIE.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) f x i

theorem peetre (x y : V) : 1 + ‖y‖ ≤ (1 + ‖x + y‖) * (1 + ‖x‖) := by
  have h : ‖y‖ ≤ ‖x + y‖ + ‖x‖ := by
    have := norm_sub_le (x + y) x
    simpa using this
  nlinarith [norm_nonneg (x + y), norm_nonneg x, mul_nonneg (norm_nonneg (x + y)) (norm_nonneg x)]

theorem diffFun_bound (f : SchwartzMap V ℂ) (k n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : V,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (diffFun f y) x‖ * (1 + ‖y‖) ^ K ≤ C := by
  set M : ℝ := 2 ^ (K + k) *
    ((Finset.Iic (K + k, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f with hM
  have hM0 : 0 ≤ M := by
    rw [hM]; exact mul_nonneg (by positivity) (apply_nonneg _ _)
  have hA : ∀ i, i ≤ n → ∀ z : V, (1 + ‖z‖) ^ (K + k) * ‖iteratedFDeriv ℝ i f z‖ ≤ M := by
    intro i hi z
    exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K + k, n)) le_rfl hi f z
  have hB : ∀ i, i ≤ n → ∀ z : V, (1 + ‖z‖) ^ K * ‖iteratedFDeriv ℝ i f z‖ ≤ M := by
    intro i hi z
    refine le_trans ?_ (hA i hi z)
    have h1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 (Nat.le_add_right _ _)) (norm_nonneg _)
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (M * M), by positivity, fun x y => ?_⟩
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (contDiff_translate f y) (contDiff_conj f) x (n := n) (by exact_mod_cast le_top)
  have hw : ‖x‖ ^ k * (1 + ‖y‖) ^ K ≤ (1 + ‖x + y‖) ^ K * (1 + ‖x‖) ^ (K + k) := by
    have h1 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
    have h2 : (1 + ‖y‖) ^ K ≤ ((1 + ‖x + y‖) * (1 + ‖x‖)) ^ K :=
      pow_le_pow_left₀ (by positivity) (peetre x y) _
    calc ‖x‖ ^ k * (1 + ‖y‖) ^ K ≤ (1 + ‖x‖) ^ k * ((1 + ‖x + y‖) * (1 + ‖x‖)) ^ K := by
          gcongr
      _ = _ := by rw [mul_pow, pow_add]; ring
  have hw0 : 0 ≤ ‖x‖ ^ k * (1 + ‖y‖) ^ K := by positivity
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (diffFun f y) x‖ * (1 + ‖y‖) ^ K
      = (‖x‖ ^ k * (1 + ‖y‖) ^ K) * ‖iteratedFDeriv ℝ n (diffFun f y) x‖ := by ring
    _ ≤ (‖x‖ ^ k * (1 + ‖y‖) ^ K) * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x => f (x + y)) x‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun x => conj (f x)) x‖ :=
        mul_le_mul_of_nonneg_left hL hw0
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((‖x‖ ^ k * (1 + ‖y‖) ^ K) *
          (‖iteratedFDeriv ℝ i f (x + y)‖ * ‖iteratedFDeriv ℝ (n - i) f x‖)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_iteratedFDeriv_conj, iteratedFDeriv_comp_add_right]
        ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (M * M) := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        calc _ ≤ ((1 + ‖x + y‖) ^ K * (1 + ‖x‖) ^ (K + k)) *
              (‖iteratedFDeriv ℝ i f (x + y)‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) :=
              mul_le_mul_of_nonneg_right hw (by positivity)
          _ = ((1 + ‖x + y‖) ^ K * ‖iteratedFDeriv ℝ i f (x + y)‖) *
              ((1 + ‖x‖) ^ (K + k) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
          _ ≤ M * M := mul_le_mul (hB i hi' _) (hA _ (Nat.sub_le _ _) _)
              (by positivity) hM0

def diffS (f : SchwartzMap V ℂ) (y : V) : SchwartzMap V ℂ where
  toFun := diffFun f y
  smooth' := contDiff_diffFun f y
  decay' := by
    intro k n
    obtain ⟨C, -, hC⟩ := diffFun_bound f k n 0
    exact ⟨C, fun x => by simpa using hC x y⟩

theorem diffS_apply (f : SchwartzMap V ℂ) (y x : V) :
    diffS f y x = f (x + y) * conj (f x) := rfl

theorem seminorm_diffS_le (f : SchwartzMap V ℂ) (k n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : V,
      SchwartzMap.seminorm ℂ k n (diffS f y) ≤ C * ((1 + ‖y‖) ^ K)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := diffFun_bound f k n K
  refine ⟨C, hC0, fun y => ?_⟩
  have hy : 0 < (1 + ‖y‖) ^ K := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  rw [← div_eq_mul_inv, le_div_iff₀ hy]
  exact hC x y

theorem continuous_seminorm_diffS_le (f : SchwartzMap V ℂ) (K : ℕ)
    (p : Seminorm ℂ (SchwartzMap V ℂ)) (hp : Continuous p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : V, p (diffS f y) ≤ C * ((1 + ‖y‖) ^ K)⁻¹ := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) p hp
  choose D hD0 hD using fun m : ℕ × ℕ => seminorm_diffS_le f m.1 m.2 K
  refine ⟨C * ∑ m ∈ s, D m, mul_nonneg C.2 (Finset.sum_nonneg fun m _ => hD0 m), fun y => ?_⟩
  have hw : 0 ≤ ((1 + ‖y‖) ^ K)⁻¹ := by positivity
  have hsup : (s.sup (schwartzSeminormFamily ℂ V ℂ)) (diffS f y) ≤
      (∑ m ∈ s, D m) * ((1 + ‖y‖) ^ K)⁻¹ := by
    refine Seminorm.finset_sup_apply_le
      (mul_nonneg (Finset.sum_nonneg fun m _ => hD0 m) hw) fun m hm => ?_
    refine (hD m y).trans (mul_le_mul_of_nonneg_right ?_ hw)
    exact Finset.single_le_sum (f := D) (fun i _ => hD0 i) hm
  calc p (diffS f y) ≤ (C • s.sup (schwartzSeminormFamily ℂ V ℂ)) (diffS f y) := hC _
    _ = (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) (diffS f y) := rfl
    _ ≤ (C : ℝ) * ((∑ m ∈ s, D m) * ((1 + ‖y‖) ^ K)⁻¹) :=
        mul_le_mul_of_nonneg_left hsup C.2
    _ = _ := by ring

end Decay

section Fourier

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem fourier_diffS_decay (f : SchwartzMap V ℂ) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ξ : V,
      ‖𝓕 (diffS f y) ξ‖ ≤ C * (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖ξ‖) ^ K)⁻¹) := by
  have hp : ∀ m : ℕ × ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : V,
      SchwartzMap.seminorm ℂ m.1 m.2 (𝓕 (diffS f y)) ≤ C * ((1 + ‖y‖) ^ K)⁻¹ := by
    intro m
    refine continuous_seminorm_diffS_le f K
      ((SchwartzMap.seminorm ℂ m.1 m.2).comp
        (SchwartzMap.fourierTransformCLM ℂ (V := V) (E := ℂ)).toLinearMap) ?_
    exact ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm m).comp
      (SchwartzMap.fourierTransformCLM ℂ (V := V) (E := ℂ)).continuous
  choose D hD0 hD using hp
  set s := Finset.Iic ((K, 0) : ℕ × ℕ)
  refine ⟨2 ^ K * ∑ m ∈ s, D m,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => hD0 m), fun y ξ => ?_⟩
  have hy : 0 ≤ ((1 + ‖y‖) ^ K)⁻¹ := by positivity
  have hξ : 0 < (1 + ‖ξ‖) ^ K := by positivity
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K, 0)) (k := K) (n := 0)
    le_rfl le_rfl (𝓕 (diffS f y)) ξ
  have hsup : (s.sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) (𝓕 (diffS f y)) ≤
      (∑ m ∈ s, D m) * ((1 + ‖y‖) ^ K)⁻¹ := by
    refine Seminorm.finset_sup_apply_le
      (mul_nonneg (Finset.sum_nonneg fun m _ => hD0 m) hy) fun m hm => ?_
    refine (hD m y).trans (mul_le_mul_of_nonneg_right ?_ hy)
    exact Finset.single_le_sum (f := D) (fun i _ => hD0 i) hm
  rw [norm_iteratedFDeriv_zero] at h1
  have h2 : (1 + ‖ξ‖) ^ K * ‖𝓕 (diffS f y) ξ‖ ≤ 2 ^ K * ((∑ m ∈ s, D m) * ((1 + ‖y‖) ^ K)⁻¹) :=
    h1.trans (mul_le_mul_of_nonneg_left hsup (by positivity))
  have h3 : ‖𝓕 (diffS f y) ξ‖ ≤ 2 ^ K * ((∑ m ∈ s, D m) * ((1 + ‖y‖) ^ K)⁻¹) / (1 + ‖ξ‖) ^ K := by
    rw [le_div_iff₀ hξ]; linarith
  calc _ ≤ _ := h3
    _ = _ := by rw [div_eq_mul_inv]; ring

def ee (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ))

theorem ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  simp only [ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  have : 2 * (Real.pi : ℂ) * Complex.I * ((t : ℝ) : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [ee, this, Complex.norm_exp_ofReal_mul_I]

theorem conj_ee (t : ℝ) : conj (ee t) = ee (-t) := by
  rw [ee, ee, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem continuous_ee : Continuous ee := by
  unfold ee
  fun_prop

theorem enorm_sq_le (f : SchwartzMap V ℂ) (q : V → ℝ) (T : V →ₗ[ℝ] V) (hq : Continuous q)
    (hT : ∀ x y, q (x + y) = q x + q y + inner ℝ x (T y)) :
    ENNReal.ofReal (‖∫ x, f x * ee (q x)‖ ^ 2) ≤ ∫⁻ y, ‖𝓕 (diffS f y) (-(T y))‖ₑ := by
  set v : V → ℂ := fun x => f x * ee (q x) with hv
  set u : V → ℂ := fun x => conj (v x) with hu
  have hvc : Continuous v := f.continuous.mul (continuous_ee.comp hq)
  have hvi : Integrable v := by
    refine f.integrable.mono hvc.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    simp [hv, norm_ee]
  have hui : Integrable u := by
    refine hvi.mono (Complex.continuous_conj.comp hvc).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    simp [hu]
  have hh : Integrable (fun z : V × V => u z.1 * v z.2) (volume.prod volume) := hui.mul_prod hvi
  have mp := measurePreserving_prod_add (volume : Measure V) (volume : Measure V)
  set F : V × V → ℂ := fun z => u z.1 * v (z.1 + z.2) with hF
  have hFi : Integrable F (volume.prod volume) := mp.integrable_comp_of_integrable hh
  have e1 : ∫ z : V × V, u z.1 * v z.2 ∂(volume.prod volume) =
      ∫ z : V × V, F z ∂(volume.prod volume) := by
    conv_lhs => rw [← mp.map_eq]
    exact integral_map mp.measurable.aemeasurable (by rw [mp.map_eq]; exact hh.aestronglyMeasurable)
  have e2 : ∀ y : V, ∫ x, F (x, y) = ee (q y) * 𝓕 (diffS f y) (-(T y)) := by
    intro y
    rw [SchwartzMap.fourier_coe, Real.fourier_eq', ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have hx : Complex.exp (((-2 * Real.pi * inner ℝ x (-(T y)) : ℝ) : ℂ) * Complex.I) =
        ee (inner ℝ x (T y)) := by
      rw [ee]
      congr 1
      rw [inner_neg_right]
      push_cast
      ring
    simp only [hF, hu, hv, hx, diffS_apply, smul_eq_mul, map_mul, conj_ee, hT x y, ee_add]
    have h1 : ee (-q x) * ee (q x) = 1 := by
      rw [← ee_add]; simp [ee]
    linear_combination (conj (f x) * f (x + y) * ee (q y) * ee (inner ℝ x (T y))) * h1
  have e3 : conj (∫ x, v x) * ∫ x, v x = ∫ y, ee (q y) * 𝓕 (diffS f y) (-(T y)) := by
    rw [← integral_conj, ← integral_prod_mul u v, e1, integral_prod_symm F hFi]
    exact integral_congr_ae (ae_of_all _ e2)
  have e4 : ENNReal.ofReal (‖∫ x, v x‖ ^ 2) = ‖conj (∫ x, v x) * ∫ x, v x‖ₑ := by
    rw [← ofReal_norm, norm_mul, Complex.norm_conj, sq]
  rw [e4, e3]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  refine lintegral_congr fun y => ?_
  rw [enorm_mul, ← ofReal_norm (ee _), norm_ee]
  simp

theorem weyl_differencing (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (f : SchwartzMap V ℂ) (K : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : V → ℝ) (T : V →ₗ[ℝ] V), Continuous q →
      (∀ x y, q (x + y) = q x + q y + inner ℝ x (T y)) →
      ENNReal.ofReal (‖∫ x, f x * Complex.exp (2 * Real.pi * Complex.I * ((q x : ℝ) : ℂ))‖ ^ 2) ≤
        ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖T y‖) ^ K)⁻¹) := by
  obtain ⟨C, hC0, hC⟩ := fourier_diffS_decay f K
  refine ⟨C, hC0, fun q T hq hT => (enorm_sq_le f q T hq hT).trans ?_⟩
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  rw [← ENNReal.ofReal_mul hC0, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa using hC y (-(T y))

end Fourier

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
