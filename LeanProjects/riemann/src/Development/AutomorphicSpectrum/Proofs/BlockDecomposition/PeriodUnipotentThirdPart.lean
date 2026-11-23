import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding

noncomputable section

open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C
open scoped FourierTransform SchwartzMap RealInnerProductSpace

namespace GlobalTheory.CompanionTheory.PerUThree

theorem integral_inv_neg (G : ℝ → ℂ) :
    ∫ x : ℝ, ((|x|⁻¹ : ℝ) : ℂ) * G x = ∫ r : ℝ, ((|r|⁻¹ : ℝ) : ℂ) * G (-r⁻¹) := by
  have hR : (volume : Measure ℝ).restrict ({0}ᶜ : Set ℝ) = volume :=
    Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.2 (by simp))
  have hs : MeasurableSet ({0}ᶜ : Set ℝ) := (measurableSet_singleton 0).compl
  have himg : (fun r : ℝ => -r⁻¹) '' ({0}ᶜ : Set ℝ) = {0}ᶜ := by
    ext y
    constructor
    · rintro ⟨r, hr, rfl⟩
      simpa using hr
    · intro hy
      refine ⟨-y⁻¹, by simpa using hy, by simp⟩
  have hd : ∀ x ∈ ({0}ᶜ : Set ℝ), HasDerivWithinAt (fun r : ℝ => -r⁻¹) ((x ^ 2)⁻¹) {0}ᶜ x := by
    intro x hx
    have h := (hasDerivAt_inv (show x ≠ 0 from hx)).fun_neg
    rw [neg_neg] at h
    exact h.hasDerivWithinAt
  have hinj : Set.InjOn (fun r : ℝ => -r⁻¹) ({0}ᶜ : Set ℝ) := by
    intro a _ b _ hab
    simpa using hab
  have key := integral_image_eq_integral_abs_deriv_smul hs hd hinj
    (fun x : ℝ => ((|x|⁻¹ : ℝ) : ℂ) * G x)
  rw [himg, hR] at key
  rw [key]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with r hr
  have hr0 : r ≠ 0 := hr
  have ha : |r| ≠ 0 := abs_ne_zero.2 hr0
  rw [Complex.real_smul]
  simp only [abs_neg, abs_inv, inv_inv, abs_pow, sq_abs]
  rw [← mul_assoc]
  congr 1
  push_cast
  have hc : ((|r| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha
  have h2 : (r : ℂ) ^ 2 = ((|r| : ℝ) : ℂ) ^ 2 := by exact_mod_cast (sq_abs r).symm
  rw [h2]
  field_simp

theorem sign_id (δ : Bool) (s : ℂ) {r : ℝ} (hr : r ≠ 0) :
    cr δ s (-r⁻¹) * sg (-r⁻¹) * ((|(-r⁻¹)|⁻¹ : ℝ) : ℂ) =
      cr (!δ) 0 (-1) * cr (!δ) (1 - s) r := by
  have ha : (0 : ℝ) < |r| := abs_pos.2 hr
  have hc : ((|r| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hpow : ((|(-r⁻¹)| : ℝ) : ℂ) ^ s * ((|r| : ℝ) : ℂ) = ((|r| : ℝ) : ℂ) ^ (1 - s) := by
    have : ((|(-r⁻¹)| : ℝ) : ℂ) = (((|r| : ℝ) : ℂ))⁻¹ := by simp
    rw [this, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg ha.le]; exact Real.pi_pos.ne), Complex.cpow_sub _ _ hc,
      Complex.cpow_one]
    field_simp
  have habs : ((|(-r⁻¹)|⁻¹ : ℝ) : ℂ) = ((|r| : ℝ) : ℂ) := by simp
  rcases lt_or_gt_of_ne hr with h | h
  · have h1 : ¬ (-r⁻¹ < 0) := by
      have := inv_lt_zero.2 h
      linarith
    cases δ <;> simp [cr, sg, h, h1] at hpow ⊢ <;> exact hpow
  · have h1 : -r⁻¹ < 0 := by
      have := inv_pos.2 h
      linarith
    have h2 : ¬ r < 0 := not_lt.2 h.le
    cases δ <;> simp [cr, sg, h1, h2] at hpow ⊢ <;> exact hpow

theorem integrable_K {a : ℝ} (h1 : -1 < a) (h2 : a < 1) :
    Integrable (fun w : ℝ => |w| ^ a * ((1 + |w|) ^ 2)⁻¹) := by
  set f : ℝ → ℝ := fun w => |w| ^ a * ((1 + |w|) ^ 2)⁻¹ with hf
  have hfm : Measurable f := by
    apply Measurable.mul
    · exact (measurable_id.abs).pow_const a
    · fun_prop
  have hA : IntegrableOn f (Set.Ioc 0 1) := by
    have hb : IntegrableOn (fun x : ℝ => x ^ a) (Set.Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' h1)
    refine Integrable.mono' hb hfm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
    have hw0 : 0 < w := hw.1
    rw [hf]
    simp only [abs_of_pos hw0, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    have : ((1 + w) ^ 2)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      nlinarith
    calc w ^ a * ((1 + w) ^ 2)⁻¹ ≤ w ^ a * 1 := by gcongr
      _ = w ^ a := mul_one _
  have hB : IntegrableOn f (Set.Ioi 1) := by
    have hb : IntegrableOn (fun x : ℝ => x ^ (a - 2)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine Integrable.mono' hb hfm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hw0 : 0 < w := lt_trans one_pos hw
    rw [hf]
    simp only [abs_of_pos hw0, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), Real.rpow_sub hw0, Real.rpow_two, div_eq_mul_inv]
    have : ((1 + w) ^ 2)⁻¹ ≤ (w ^ 2)⁻¹ := by
      apply inv_anti₀ (by positivity)
      nlinarith
    gcongr
  have hC : IntegrableOn f (Set.Ioi 0) := by
    have : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
    rw [this]
    exact hA.union hB
  have hg : Integrable ((Set.Ioi (0 : ℝ)).indicator f) :=
    hC.integrable_indicator measurableSet_Ioi
  refine (hg.add hg.comp_neg).congr ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with w hw
  have hw0 : w ≠ 0 := hw
  have hfe : f (-w) = f w := by simp [hf]
  rcases lt_or_gt_of_ne hw0 with h | h
  · simp [Set.indicator, h, not_lt.2 h.le, hfe]
  · simp [Set.indicator, h, not_lt.2 h.le]

abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

def gx (Ψ : M23 → ℂ) (h : M22) (x : Fin 2 → ℝ) : ℂ := Ψ (Matrix.of.symm (Matrix.of h * blk x))

def Qf (Ψ : M23 → ℂ) (h : M22) (w : ℝ) : ℂ := ∫ x0 : ℝ, gx Ψ h ![x0, w]

def cst (h : M22) : M23 := fun i => ![h i 0, h i 1, 0]

def ell (h : M22) : E2 →ₗ[ℝ] M23 where
  toFun y := fun i => ![0, 0, h i 0 * y 0 + h i 1 * y 1]
  map_add' a b := by
    funext i j
    fin_cases j <;> simp <;> ring
  map_smul' c a := by
    funext i j
    fin_cases j <;> simp <;> ring

theorem affine_eq (h : M22) (y : E2) :
    Matrix.of.symm (Matrix.of h * blk y.ofLp) = cst h + ell h y := by
  funext i j
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, blk, cst, ell, Fin.sum_univ_three]

theorem ell_ker (h : M22) (hdet : (Matrix.of h).det ≠ 0) : LinearMap.ker (ell h) = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 fun y hy => ?_
  have h1 : ∀ i, h i 0 * y 0 + h i 1 * y 1 = 0 := by
    intro i
    simpa [ell] using congr_fun (congr_fun hy i) 2
  have h2 : (Matrix.of h).mulVec y.ofLp = 0 := by
    funext i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h1 i
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hdet h2
  ext i
  simpa using congr_fun h3 i

def psiS (Ψ : M23 → ℂ) (hsm : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hdec : ∀ n : ℕ, ∃ C : ℝ, ∀ m ≤ n, ∀ X : M23, (1 + ‖X‖) ^ n * ‖iteratedFDeriv ℝ m Ψ X‖ ≤ C) :
    𝓢(M23, ℂ) where
  toFun := Ψ
  smooth' := hsm
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := hdec (max k n)
    refine ⟨C, fun x => ?_⟩
    refine le_trans ?_ (hC n (le_max_right _ _) x)
    gcongr
    calc ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith
      _ ≤ (1 + ‖x‖) ^ (max k n) :=
        pow_le_pow_right₀ (by linarith [norm_nonneg x]) (le_max_left _ _)

theorem exists_schwartz (Ψ : M23 → ℂ) (hsm : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hdec : ∀ n : ℕ, ∃ C : ℝ, ∀ m ≤ n, ∀ X : M23, (1 + ‖X‖) ^ n * ‖iteratedFDeriv ℝ m Ψ X‖ ≤ C)
    (h : M22) (hdet : (Matrix.of h).det ≠ 0) :
    ∃ S : 𝓢(E2, ℂ), ∀ y : E2, S y = gx Ψ h y.ofLp := by
  obtain ⟨K, -, hK⟩ := LinearMap.exists_antilipschitzWith (ell h) (ell_ker h hdet)
  have hA : AntilipschitzWith K (fun y : E2 => cst h + ell h y) :=
    AntilipschitzWith.of_le_mul_dist fun a b => by
      simpa [dist_add_left] using hK.le_mul_dist a b
  have hT : Function.HasTemperateGrowth (fun y : E2 => cst h + ell h y) :=
    (Function.HasTemperateGrowth.const (cst h)).add
      (LinearMap.toContinuousLinearMap (ell h)).hasTemperateGrowth
  refine ⟨SchwartzMap.compCLMOfAntilipschitz ℂ hT hA (psiS Ψ hsm hdec), fun y => ?_⟩
  simp only [SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp, gx]
  rw [affine_eq]
  rfl

theorem schwartz_bd (S : 𝓢(E2, ℂ)) (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, (1 + ‖y‖) ^ k * ‖S y‖ ≤ C := by
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S,
    by positivity, fun y => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
    le_rfl le_rfl S y
  simpa using this

theorem gx_decay {Ψ : M23 → ℂ} {h : M22} {S : 𝓢(E2, ℂ)} (hS : ∀ y : E2, S y = gx Ψ h y.ofLp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, ‖gx Ψ h ![a, b]‖ ≤ C * (((1 + |a|) ^ 2)⁻¹ * ((1 + |b|) ^ 2)⁻¹) := by
  obtain ⟨C, hC0, hC⟩ := schwartz_bd S 4
  refine ⟨C, hC0, fun a b => ?_⟩
  set y : E2 := WithLp.toLp 2 ![a, b] with hy
  have hya : |a| ≤ ‖y‖ := by simpa [hy] using PiLp.norm_apply_le y 0
  have hyb : |b| ≤ ‖y‖ := by simpa [hy] using PiLp.norm_apply_le y 1
  have h1 := hC y
  rw [hS y, show y.ofLp = ![a, b] from rfl] at h1
  have hp : 0 < (1 + |a|) ^ 2 * (1 + |b|) ^ 2 := by positivity
  rw [← mul_inv, ← div_eq_mul_inv, le_div_iff₀ hp]
  refine le_trans ?_ h1
  rw [mul_comm]
  gcongr ?_ * _
  calc (1 + |a|) ^ 2 * (1 + |b|) ^ 2 ≤ (1 + ‖y‖) ^ 2 * (1 + ‖y‖) ^ 2 := by gcongr
    _ = (1 + ‖y‖) ^ 4 := by ring

theorem innB_eq {Ψ : M23 → ℂ} {h : M22} {S : 𝓢(E2, ℂ)} (hS : ∀ y : E2, S y = gx Ψ h y.ofLp)
    (β : ℝ) : B.innB Ψ h β = (𝓕 S : 𝓢(E2, ℂ)) (WithLp.toLp 2 ![0, -β]) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  have hmp := PiLp.volume_preserving_toLp (Fin 2)
  rw [← hmp.integral_comp (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding]
  unfold B.innB
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hin : inner ℝ (WithLp.toLp 2 x : E2) (WithLp.toLp 2 ![0, -β] : E2) = -β * x 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
  beta_reduce
  rw [hin, hS, smul_eq_mul, mul_comm]
  simp only [gx, psiR, WithLp.ofLp_toLp]
  congr 2
  push_cast
  ring

theorem fin_two_integral (F : (Fin 2 → ℝ) → ℂ) (hF : Integrable (fun p : ℝ × ℝ => F ![p.1, p.2])) :
    ∫ x, F x = ∫ w : ℝ, ∫ x0 : ℝ, F ![x0, w] := by
  have hmp := (volume_preserving_finTwoArrow ℝ).symm
  rw [← hmp.integral_comp']
  exact integral_prod_symm (f := fun p : ℝ × ℝ => F ![p.1, p.2]) hF

theorem continuous_G {Ψ : M23 → ℂ} {h : M22} {S : 𝓢(E2, ℂ)} (hS : ∀ y : E2, S y = gx Ψ h y.ofLp) :
    Continuous (fun p : ℝ × ℝ => gx Ψ h ![p.1, p.2]) := by
  have h1 : Continuous (fun p : ℝ × ℝ => (WithLp.toLp 2 ![p.1, p.2] : E2)) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  have h2 := S.continuous.comp h1
  refine h2.congr fun p => ?_
  simpa using hS (WithLp.toLp 2 ![p.1, p.2])

theorem joint_int {Ψ : M23 → ℂ} {h : M22} {S : 𝓢(E2, ℂ)} (hS : ∀ y : E2, S y = gx Ψ h y.ofLp)
    {W : ℝ → ℂ} (hWm : Measurable W) {a : ℝ} (h1 : -1 < a) (h2 : a < 1)
    (hW : ∀ w, ‖W w‖ ≤ |w| ^ a) :
    Integrable (fun p : ℝ × ℝ => W p.2 * gx Ψ h ![p.1, p.2]) := by
  obtain ⟨C, hC0, hC⟩ := gx_decay hS
  have hu : Integrable (fun w : ℝ => ((1 + |w|) ^ 2)⁻¹) := by
    simpa using integrable_K (a := 0) (by norm_num) (by norm_num)
  have hv := integrable_K h1 h2
  have hd := (hu.mul_prod hv).const_mul C
  refine hd.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact ((hWm.comp measurable_snd).aestronglyMeasurable).mul
      (continuous_G hS).aestronglyMeasurable
  · rw [norm_mul]
    have e := hC p.1 p.2
    calc ‖W p.2‖ * ‖gx Ψ h ![p.1, p.2]‖
        ≤ |p.2| ^ a * (C * (((1 + |p.1|) ^ 2)⁻¹ * ((1 + |p.2|) ^ 2)⁻¹)) := by
          gcongr
          exact hW _
      _ = _ := by ring

theorem integral_fubini_last_coordinate {Ψ : M23 → ℂ} {h : M22} {W : ℝ → ℂ}
    (hJ : Integrable (fun p : ℝ × ℝ => W p.2 * gx Ψ h ![p.1, p.2])) :
    ∫ x, W (x 1) * gx Ψ h x = ∫ w, W w * Qf Ψ h w := by
  rw [fin_two_integral (fun x => W (x 1) * gx Ψ h x) (by simpa using hJ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [Qf]
  rw [← integral_const_mul]
  simp

theorem marg_int {Ψ : M23 → ℂ} {h : M22} {W : ℝ → ℂ}
    (hJ : Integrable (fun p : ℝ × ℝ => W p.2 * gx Ψ h ![p.1, p.2])) :
    Integrable (fun w => W w * Qf Ψ h w) := by
  refine hJ.integral_prod_right.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [Qf]
  rw [← integral_const_mul]

theorem psi_meas (r : ℝ) : Measurable (fun w : ℝ => psiR (r * w)) := by
  unfold psiR
  fun_prop

theorem psi_norm (x : ℝ) : ‖psiR x‖ = 1 := by
  have : -2 * (Real.pi : ℂ) * I * x = ((-2 * Real.pi * x : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [psiR, this, Complex.norm_exp_ofReal_mul_I]

theorem fourier_Q {Ψ : M23 → ℂ} {h : M22} {S : 𝓢(E2, ℂ)} (hS : ∀ y : E2, S y = gx Ψ h y.ofLp)
    (r : ℝ) : 𝓕 (Qf Ψ h) r = B.innB Ψ h (-r) := by
  have hJ := joint_int hS (psi_meas r) (a := 0) (by norm_num) (by norm_num)
    (fun w => by simp [psi_norm])
  have h1 : B.innB Ψ h (-r) = ∫ x, psiR (r * x 1) * gx Ψ h x := by
    unfold B.innB
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [gx, neg_mul, neg_neg]
    ring
  rw [h1]
  refine Eq.trans ?_ (integral_fubini_last_coordinate (W := fun w => psiR (r * w)) hJ).symm
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [psiR, smul_eq_mul]
  congr 2
  push_cast
  ring

theorem fourier_Q_int {Ψ : M23 → ℂ} {h : M22} {S : 𝓢(E2, ℂ)} (hS : ∀ y : E2, S y = gx Ψ h y.ofLp)
    {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    Integrable (fun r => 𝓕 (Qf Ψ h) r * ((|r| ^ (-σ) : ℝ) : ℂ)) := by
  obtain ⟨C, hC0, hC⟩ := schwartz_bd (𝓕 S : 𝓢(E2, ℂ)) 2
  have hF : ∀ r, 𝓕 (Qf Ψ h) r = (𝓕 S : 𝓢(E2, ℂ)) (WithLp.toLp 2 ![0, r]) := by
    intro r
    rw [fourier_Q hS, innB_eq hS, neg_neg]
  have hc : Continuous (fun r : ℝ => (𝓕 S : 𝓢(E2, ℂ)) (WithLp.toLp 2 ![0, r])) := by
    refine (𝓕 S : 𝓢(E2, ℂ)).continuous.comp ((PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun i => ?_))
    fin_cases i <;> simp <;> fun_prop
  have hv := (integrable_K (a := -σ) (by linarith) (by linarith)).const_mul C
  simp only [hF]
  refine hv.mono' (hc.aestronglyMeasurable.mul ?_) (Filter.Eventually.of_forall fun r => ?_)
  · exact (Complex.measurable_ofReal.comp
      ((measurable_id.abs).pow_const (-σ))).aestronglyMeasurable
  · set y : E2 := WithLp.toLp 2 ![0, r] with hy
    have hyr : |r| ≤ ‖y‖ := by simpa [hy] using PiLp.norm_apply_le y 1
    have h2 := hC y
    have hp : 0 < (1 + |r|) ^ 2 := by positivity
    have h3 : ‖(𝓕 S : 𝓢(E2, ℂ)) y‖ ≤ C * ((1 + |r|) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hp]
      refine le_trans ?_ h2
      rw [mul_comm]
      gcongr
    have hn : 0 ≤ |r| ^ (-σ) := Real.rpow_nonneg (abs_nonneg _) _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hn]
    calc ‖(𝓕 S : 𝓢(E2, ℂ)) y‖ * |r| ^ (-σ) ≤ C * ((1 + |r|) ^ 2)⁻¹ * |r| ^ (-σ) := by gcongr
      _ = _ := by ring

theorem cr_sub_one (e : Bool) (s : ℂ) {w : ℝ} (hw : w ≠ 0) :
    ((|w|⁻¹ : ℝ) : ℂ) * cr e s w = cr e (s - 1) w := by
  have hc : ((|w| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.2 hw
  simp only [cr]
  rw [Complex.cpow_sub _ _ hc, Complex.cpow_one]
  push_cast
  field_simp

theorem cr_meas (e : Bool) (s : ℂ) : Measurable (cr e s) := by
  unfold cr
  refine Measurable.mul ?_ ?_
  · cases e
    · simp
    · simpa using Measurable.ite measurableSet_Iio measurable_const measurable_const
  · exact (Complex.measurable_ofReal.comp measurable_id.abs).pow_const s

theorem cr_norm (e : Bool) {s : ℂ} (hs : s.re ≠ 0) (w : ℝ) : ‖cr e s w‖ = |w| ^ s.re := by
  have h1 : ‖(if (e = true ∧ w < 0) then (-1 : ℂ) else 1)‖ = 1 := by
    split_ifs <;> simp
  rw [cr, norm_mul, h1, one_mul, Complex.norm_cpow_eq_rpow_re_of_nonneg (abs_nonneg w) hs]

theorem zeta_integral_first_formula (Q : ℝ → ℂ) (e : Bool) (s : ℂ) : z1 Q e s = ∫ w, cr e (s - 1) w * Q w := by
  have h1 : z1 Q e s = ∫ a : ℝˣ, (fun x : ℝ => Q x * cr e s x) a ∂mulR := rfl
  rw [h1, GlobalTheory.CompanionTheory.TateR.integral_mulR (fun x : ℝ => Q x * cr e s x)]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with w hw
  rw [← cr_sub_one e s hw]
  ring

theorem left_side (δ : Bool) (s : ℂ) (Ψ : M23 → ℂ) (h : M22) (F : ℝ → ℂ)
    (hF : ∀ r, F r = B.innB Ψ h (-r)) :
    ∫ t : ℝˣ, chR δ s t * sg t * (((|(t : ℝ)|)⁻¹ : ℝ) : ℂ) * B.innB Ψ h (t : ℝ)⁻¹ ∂mulR =
      cr (!δ) 0 (-1) * z1 F (!δ) (1 - s) := by
  have h1 : ∫ t : ℝˣ, chR δ s t * sg t * (((|(t : ℝ)|)⁻¹ : ℝ) : ℂ) * B.innB Ψ h (t : ℝ)⁻¹ ∂mulR =
      ∫ t : ℝˣ, (fun x : ℝ => cr δ s x * sg x * ((|x|⁻¹ : ℝ) : ℂ) * B.innB Ψ h x⁻¹) t ∂mulR := rfl
  have h2 : z1 F (!δ) (1 - s) = ∫ a : ℝˣ, (fun x : ℝ => F x * cr (!δ) (1 - s) x) a ∂mulR := rfl
  rw [h1, h2,
    GlobalTheory.CompanionTheory.TateR.integral_mulR (fun x : ℝ => cr δ s x * sg x * ((|x|⁻¹ : ℝ) : ℂ) * B.innB Ψ h x⁻¹),
    GlobalTheory.CompanionTheory.TateR.integral_mulR (fun x : ℝ => F x * cr (!δ) (1 - s) x), integral_inv_neg,
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with r hr
  have hr0 : r ≠ 0 := hr
  have e := sign_id δ s hr0
  simp only [inv_neg, inv_inv]
  rw [hF r]
  simp only [abs_neg, abs_inv, inv_inv] at e ⊢
  linear_combination (((|r|⁻¹ : ℝ) : ℂ) * B.innB Ψ h (-r)) * e

theorem main : TateFunctionalEquationComplex → UnipotentTateFunctionalEquation := by
  intro hT Ψ δ s h0 h1 hsm hdec h hdet
  obtain ⟨S, hS⟩ := exists_schwartz Ψ hsm hdec h hdet
  have hσ : (s - 1).re ≠ 0 := by
    simp only [sub_re, one_re]
    linarith
  have hQ1 : Integrable (Qf Ψ h) := by
    have := marg_int (W := fun _ => 1) (joint_int hS (W := fun _ => 1) measurable_const (a := 0) (by norm_num)
      (by norm_num) (fun w => by simp))
    simpa using this
  have hQ2 : Integrable (fun w => Qf Ψ h w * ((|w| ^ (s.re - 1) : ℝ) : ℂ)) := by
    have hm : Measurable (fun w : ℝ => ((|w| ^ (s.re - 1) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp ((measurable_id.abs).pow_const _)
    have := marg_int (W := fun w : ℝ => ((|w| ^ (s.re - 1) : ℝ) : ℂ)) (joint_int hS hm (a := s.re - 1) (by linarith) (by linarith)
      (fun w => by
        rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]))
    simpa [mul_comm] using this
  have hFE := hT (Qf Ψ h) (!δ) s h0 h1 hQ1 hQ2 (fourier_Q_int hS h0 h1)
  have hJ := joint_int hS (cr_meas (!δ) (s - 1)) (a := s.re - 1) (by linarith) (by linarith)
    (fun w => by rw [cr_norm _ hσ]; simp)
  rw [left_side δ s Ψ h (𝓕 (Qf Ψ h)) (fourier_Q hS), hFE, zeta_integral_first_formula]
  have h3 := integral_fubini_last_coordinate (W := cr (!δ) (s - 1)) hJ
  simp only [gx] at h3 ⊢
  rw [h3]
  ring

end GlobalTheory.CompanionTheory.PerUThree
