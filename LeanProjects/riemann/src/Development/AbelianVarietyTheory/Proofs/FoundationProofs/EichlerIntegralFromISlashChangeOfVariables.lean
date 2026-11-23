import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
noncomputable section
namespace GlobalTheory.EichlerChange

lemma exists_ball (z : ℂ) (hz : 0 < z.im) :
    ∃ (c : ℂ) (r : ℝ), Metric.ball c r ⊆ {u : ℂ | 0 < u.im} ∧ Complex.I ∈ Metric.ball c r ∧
      z ∈ Metric.ball c r := by
  have key : ∀ (u : ℂ) (R : ℝ), 0 < u.im → 0 < R → u.re ^ 2 + u.im ^ 2 < 2 * R * u.im →
      u ∈ Metric.ball ((R : ℂ) * Complex.I) R := by
    intro u R hu hR h
    rw [Metric.mem_ball, Complex.dist_eq, ← sq_lt_sq₀ (norm_nonneg _) hR.le, Complex.sq_norm,
      Complex.normSq_apply]
    simp
    nlinarith
  set a := (z.re ^ 2 + z.im ^ 2) / z.im with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a * z.im = z.re ^ 2 + z.im ^ 2 := by rw [ha]; field_simp
  refine ⟨((a + 1 : ℝ) : ℂ) * Complex.I, a + 1, ?_, key _ _ (by simp) (by linarith) ?_,
    key _ _ hz (by linarith) ?_⟩
  · intro u hu
    rw [Metric.mem_ball, Complex.dist_eq] at hu
    have := (Complex.abs_im_le_norm _).trans_lt hu
    simp at this
    have := (abs_lt.1 this).1
    show 0 < u.im
    linarith
  · simp; linarith
  · nlinarith [mul_nonneg ha0 hz.le]

lemma hasDerivAt_segInt (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im}) (z : ℂ)
    (hz : 0 < z.im) :
    HasDerivAt (fun τ : ℂ => ∫ t in (0 : ℝ)..1,
      g (Complex.I + t * (τ - Complex.I)) * (τ - Complex.I)) (g z) z := by
  obtain ⟨c, r, hB, hI, hzB⟩ := exists_ball z hz
  obtain ⟨G, hG⟩ := (hg.mono hB).isExactOn_ball
  refine ((hG z hzB).sub_const (G Complex.I)).congr_of_eventuallyEq ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hzB] with τ hτ
  have hmem : ∀ t ∈ Set.uIcc (0 : ℝ) 1, Complex.I + t * (τ - Complex.I) ∈ Metric.ball c r := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    simpa using (convex_ball c r).add_smul_sub_mem hI hτ ht
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => G (Complex.I + s * (τ - Complex.I)))
        (g (Complex.I + t * (τ - Complex.I)) * (τ - Complex.I)) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℂ => Complex.I + u * (τ - Complex.I)) (τ - Complex.I) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const (τ - Complex.I)).const_add Complex.I
    exact (HasDerivAt.comp (t : ℂ) (h₂ := G) (hG _ (hmem t ht)) h1).comp_ofReal
  have hc : ContinuousOn (fun t : ℝ => g (Complex.I + t * (τ - Complex.I)) * (τ - Complex.I))
      (Set.uIcc 0 1) := by
    refine ContinuousOn.mul ?_ continuousOn_const
    exact (hg.continuousOn.mono hB).comp (f := fun t : ℝ => Complex.I + t * (τ - Complex.I))
      (by fun_prop) hmem
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp

def ecoef (w : ℕ) (h : ℍ → ℂ) (n : ℕ) (v : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (h ∘ ofComplex) (Complex.I + t * (v - Complex.I)) *
    (-(Complex.I + t * (v - Complex.I))) ^ (w - n) * (v - Complex.I)

lemma coeff_eichler (w : ℕ) (h : ℍ → ℂ) (τ : ℍ) (n : ℕ) :
    (eichler w h τ).coeff n = (w.choose n : ℂ) * ecoef w h n τ := by
  unfold eichler ecoef
  rw [finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hn
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simpa using hn)]; simp

lemma hasDerivAt_ecoef (w : ℕ) (h : ℍ → ℂ) (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (n : ℕ) (z : ℂ)
    (hz : 0 < z.im) :
    HasDerivAt (ecoef w h n) ((h ∘ ofComplex) z * (-z) ^ (w - n)) z :=
  hasDerivAt_segInt (fun u => (h ∘ ofComplex) u * (-u) ^ (w - n))
    ((UpperHalfPlane.mdifferentiable_iff.1 hh).mul (by fun_prop)) z hz

lemma polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  unfold slP
  rw [LinearMap.sum_apply]
  rfl

lemma polySlash_pow (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (s z u : ℂ)
    (h1 : (g 0 0 : ℂ) - s * g 1 0 = u) (h2 : (g 0 1 : ℂ) - s * g 1 1 = -z * u) :
    slP w g ((X + C (-s)) ^ w) = C (u ^ w) * (X + C (-z)) ^ w := by
  have e : C u * (X + C (-z)) = (C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) +
      C (-s) * (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) := by
    have e1 := congrArg C h1
    have e2 := congrArg C h2
    simp only [map_sub, map_mul, map_neg] at e1 e2 ⊢
    linear_combination (-X) * e1 - e2
  rw [C_pow, ← mul_pow, e, polySlash_apply]
  conv_rhs => rw [add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_X_add_C_pow, smul_eq_C_mul, mul_pow, C_mul, C_pow, map_natCast]
  ring

lemma coe_smul_eq (σ : SL(2, ℤ)) (τ : ℍ) :
    ((σ • τ : ℍ) : ℂ) = ((mat σ 0 0 : ℂ) * τ + mat σ 0 1) / ((mat σ 1 0 : ℂ) * τ + mat σ 1 1) := by
  rw [coe_specialLinearGroup_apply]
  simp

theorem polySlash_eichler_smul (k : ℕ) (hk : 2 ≤ k) (f : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (σ : SL(2, ℤ)) : ∃ C : ℂ[X], ∀ τ : ℍ,
      slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ)) = eichler (k - 2) (f ∣[(k : ℤ)] σ) τ + C := by
  obtain ⟨w, rfl⟩ : ∃ w, k = w + 2 := ⟨k - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  set h : ℍ → ℂ := f ∣[((w + 2 : ℕ) : ℤ)] σ with hdef
  have hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    rw [hdef, ModularForm.SL_slash]
    exact hf.slash _ _
  set a : ℂ := ((mat σ 0 0 : ℤ) : ℂ) with ha
  set b : ℂ := ((mat σ 0 1 : ℤ) : ℂ) with hb
  set c : ℂ := ((mat σ 1 0 : ℤ) : ℂ) with hc
  set d : ℂ := ((mat σ 1 1 : ℤ) : ℂ) with hd
  have hdet : a * d - b * c = 1 := by
    have := σ.det_coe
    rw [Matrix.det_fin_two] at this
    rw [ha, hb, hc, hd]
    exact_mod_cast this
  refine ⟨slP w (mat σ) (eichler w f (σ • I)) - eichler w h I, fun τ => ?_⟩
  ext n
  set q : ℕ → ℂ := fun i => ((C a * X + C b) ^ i * (C c * X + C d) ^ (w - i)).coeff n with hq
  have hslP : ∀ p : ℂ[X], (slP w (mat σ) p).coeff n = ∑ i ∈ Finset.range (w + 1), p.coeff i * q i := by
    intro p
    rw [polySlash_apply, finset_sum_coeff]
    simp only [coeff_smul, smul_eq_mul]
    rfl
  set Φ : ℂ → ℂ := fun v => ∑ i ∈ Finset.range (w + 1),
      (w.choose i : ℂ) * ecoef w f i ((a * v + b) / (c * v + d)) * q i -
    (w.choose n : ℂ) * ecoef w h n v with hΦ
  have hΦ1 : ∀ τ : ℍ, Φ τ = (slP w (mat σ) (eichler w f (σ • τ))).coeff n - (eichler w h τ).coeff n := by
    intro τ
    simp only [hΦ, hslP, coeff_eichler, coe_smul_eq]
    rfl
  have hder : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt Φ 0 z := by
    intro z hz
    obtain ⟨τ, rfl⟩ : ∃ τ : ℍ, (τ : ℂ) = z := ⟨⟨z, hz⟩, rfl⟩
    have hj : c * τ + d ≠ 0 := by
      rw [hc, hd, ← ModularGroup.denom_apply]
      exact denom_ne_zero _ _
    have hs : ((σ • τ : ℍ) : ℂ) = (a * τ + b) / (c * τ + d) := coe_smul_eq σ τ
    have hm : HasDerivAt (fun v : ℂ => (a * v + b) / (c * v + d)) ((c * τ + d)⁻¹ ^ 2) (τ : ℂ) := by
      have h1 : HasDerivAt (fun v : ℂ => a * v + b) a (τ : ℂ) := by
        simpa using ((hasDerivAt_id (τ : ℂ)).const_mul a).add_const b
      have h2 : HasDerivAt (fun v : ℂ => c * v + d) c (τ : ℂ) := by
        simpa using ((hasDerivAt_id (τ : ℂ)).const_mul c).add_const d
      refine (h1.fun_div h2 hj).congr_deriv ?_
      rw [inv_pow, div_eq_mul_inv]
      linear_combination ((c * τ + d) ^ 2)⁻¹ * hdet
    have hA : ∀ i, HasDerivAt (fun v : ℂ => ecoef w f i ((a * v + b) / (c * v + d)))
        (f (σ • τ) * (-((σ • τ : ℍ) : ℂ)) ^ (w - i) * (c * τ + d)⁻¹ ^ 2) (τ : ℂ) := by
      intro i
      have := hasDerivAt_ecoef w f hf i _ (σ • τ).im_pos
      simp only [Function.comp_apply, ofComplex_apply] at this
      exact HasDerivAt.comp (τ : ℂ) (h₂ := ecoef w f i) (by rw [← hs]; exact this) hm
    have hB := hasDerivAt_ecoef w h hh n _ τ.im_pos
    simp only [Function.comp_apply, ofComplex_apply] at hB
    have hP := congrArg (fun p : ℂ[X] => p.coeff n)
      (polySlash_pow w (mat σ) ((σ • τ : ℍ) : ℂ) τ (c * τ + d)⁻¹
        (by rw [hs, ← ha, ← hc]; rw [div_eq_mul_inv]
            linear_combination (-a) * mul_inv_cancel₀ hj + (c * τ + d)⁻¹ * hdet)
        (by rw [hs, ← hb, ← hd]; rw [div_eq_mul_inv]
            linear_combination (-b) * mul_inv_cancel₀ hj - (c * τ + d)⁻¹ * τ * hdet))
    simp only [hslP, coeff_C_mul, coeff_X_add_C_pow] at hP
    have hv : h τ = f (σ • τ) * (c * τ + d)⁻¹ ^ (w + 2) := by
      rw [hdef, ModularForm.SL_slash_apply, ModularGroup.denom_apply, zpow_neg, zpow_natCast, inv_pow]
    refine ((HasDerivAt.fun_sum (u := Finset.range (w + 1)) fun i _ =>
      ((hA i).const_mul (w.choose i : ℂ)).mul_const (q i)).fun_sub
        (hB.const_mul (w.choose n : ℂ))).congr_deriv ?_
    have : ∑ i ∈ Finset.range (w + 1), (w.choose i : ℂ) *
        (f (σ • τ) * (-((σ • τ : ℍ) : ℂ)) ^ (w - i) * (c * τ + d)⁻¹ ^ 2) * q i =
        f (σ • τ) * (c * τ + d)⁻¹ ^ 2 * ∑ i ∈ Finset.range (w + 1),
          (-((σ • τ : ℍ) : ℂ)) ^ (w - i) * (w.choose i : ℂ) * q i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hP, hv]
    ring
  have hconst : Φ τ = Φ (I : ℍ) :=
    isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero (convex_halfSpace_im_gt 0).isPreconnected
      (fun z hz => (hder z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hder z hz).deriv) τ.im_pos (I : ℍ).im_pos
  rw [hΦ1, hΦ1] at hconst
  rw [coeff_add, coeff_sub]
  linear_combination hconst

end GlobalTheory.EichlerChange
