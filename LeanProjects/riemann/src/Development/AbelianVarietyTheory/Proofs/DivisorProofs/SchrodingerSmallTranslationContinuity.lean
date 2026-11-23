import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP

open scoped SchwartzMap

noncomputable section

namespace GlobalTheory.ArchUniq.SchrLip

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_iteratedFDeriv_cexp_affine (L : V →L[ℝ] ℂ) (κ : ℂ) (i : ℕ) (y : V) :
    ‖iteratedFDeriv ℝ i (fun x => Complex.exp (L x + κ)) y‖ ≤ ‖L‖ ^ i * ‖Complex.exp (L y + κ)‖ := by
  induction i generalizing y with
  | zero => simp
  | succ i ih =>
    set φ : V → ℂ := fun x => Complex.exp (L x + κ) with hφ
    have hd : ∀ x, HasFDerivAt φ (φ x • L) x := fun x =>
      ((L.hasFDerivAt (x := x)).add_const κ).cexp
    let Λ : ℂ →L[ℝ] (V →L[ℝ] ℂ) := (ContinuousLinearMap.lsmul ℝ ℂ).flip L
    have hΛ : ‖Λ‖ ≤ ‖L‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
      simp [Λ, norm_smul, mul_comm]
    have hf : fderiv ℝ φ = fun x => Λ (φ x) := funext fun x => by
      rw [(hd x).fderiv]; rfl
    have hc : ContDiff ℝ ⊤ φ := (L.contDiff.add contDiff_const).cexp
    rw [← norm_iteratedFDeriv_fderiv, hf]
    calc ‖iteratedFDeriv ℝ i (fun x => Λ (φ x)) y‖ ≤ ‖Λ‖ * ‖iteratedFDeriv ℝ i φ y‖ :=
          Λ.norm_iteratedFDeriv_comp_left (hc.of_le le_top).contDiffAt (by exact_mod_cast le_top)
      _ ≤ ‖L‖ * (‖L‖ ^ i * ‖φ y‖) := by gcongr; exact ih y
      _ = ‖L‖ ^ (i + 1) * ‖φ y‖ := by ring

theorem norm_iteratedFDeriv_le_div (h : 𝓢(V, ℂ)) (k m : ℕ) (z : V) :
    ‖iteratedFDeriv ℝ m h z‖ ≤
      2 ^ k * (Finset.Iic (k, m)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℂ p.1 p.2) h / (1 + ‖z‖) ^ k := by
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, m)) le_rfl le_rfl h z

theorem translate_sub_le (h : 𝓢(V, ℂ)) (c : V) (k m : ℕ) (y : V) :
    (1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ m (fun x => h (x + c) - h x) y‖ ≤
      2 ^ k * (1 + ‖c‖) ^ k * ‖c‖ *
        (Finset.Iic (k, m + 1)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℂ p.1 p.2) h := by
  set S := (Finset.Iic (k, m + 1)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℂ p.1 p.2) h
  have hS : 0 ≤ S := apply_nonneg _ _
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (h : V → ℂ) := h.smooth ⊤
  have hsc : ContDiff ℝ (⊤ : ℕ∞) (fun x => h (x + c)) := hsm.comp (contDiff_id.add contDiff_const)
  rw [fun_iteratedFDeriv_sub_apply (hsc.of_le (by exact_mod_cast le_top)).contDiffAt
    (hsm.of_le (by exact_mod_cast le_top)).contDiffAt, iteratedFDeriv_comp_add_right]
  have hy : 0 < (1 + ‖y‖) ^ k := by positivity
  set B := 2 ^ k * (1 + ‖c‖) ^ k * S / (1 + ‖y‖) ^ k
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ m (h : V → ℂ)) :=
    hsm.differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top m)
  have hbd : ∀ z ∈ segment ℝ y (y + c), ‖fderiv ℝ (iteratedFDeriv ℝ m (h : V → ℂ)) z‖ ≤ B := by
    intro z hz
    rw [segment_eq_image'] at hz
    obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hz
    rw [norm_fderiv_iteratedFDeriv]
    set z := y + θ • (y + c - y)
    have hzy : ‖y‖ ≤ ‖z‖ + ‖c‖ := by
      have e : y = z - θ • c := by simp [z]
      calc ‖y‖ = ‖z - θ • c‖ := by rw [← e]
        _ ≤ ‖z‖ + ‖θ • c‖ := norm_sub_le _ _
        _ ≤ ‖z‖ + ‖c‖ := by
          gcongr
          rw [norm_smul, Real.norm_of_nonneg hθ0]
          exact mul_le_of_le_one_left (norm_nonneg _) hθ1
    have h1 : 1 + ‖y‖ ≤ (1 + ‖c‖) * (1 + ‖z‖) := by nlinarith [norm_nonneg z, norm_nonneg c]
    refine (norm_iteratedFDeriv_le_div h k (m + 1) z).trans ?_
    rw [div_le_div_iff₀ (by positivity) hy]
    calc 2 ^ k * S * (1 + ‖y‖) ^ k ≤ 2 ^ k * S * ((1 + ‖c‖) * (1 + ‖z‖)) ^ k := by gcongr
      _ = 2 ^ k * (1 + ‖c‖) ^ k * S * (1 + ‖z‖) ^ k := by rw [mul_pow]; ring
  have hmv := (convex_segment y (y + c)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hdiff z) hbd (left_mem_segment ℝ y (y + c)) (right_mem_segment ℝ y (y + c))
  rw [add_sub_cancel_left] at hmv
  calc (1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ m (h : V → ℂ) (y + c) - iteratedFDeriv ℝ m (h : V → ℂ) y‖
      ≤ (1 + ‖y‖) ^ k * (B * ‖c‖) := by gcongr
    _ = 2 ^ k * (1 + ‖c‖) ^ k * ‖c‖ * S := by
      simp only [B]; field_simp

theorem norm_cexp_sub_one_le_of_re_eq_zero (w : ℂ) (hw : w.re = 0) : ‖Complex.exp w - 1‖ ≤ ‖w‖ := by
  have e : w = Complex.I * (w.im : ℂ) := by
    apply Complex.ext <;> simp [hw]
  rw [e]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  simp

theorem norm_iteratedFDeriv_cexp_sub_one_le (L : V →L[ℝ] ℂ) (κ : ℂ) (hre : ∀ x, (L x + κ).re = 0)
    {τ A : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hA : 0 ≤ A) (hL : ‖L‖ ≤ τ * A) (hκ : ‖κ‖ ≤ τ * A)
    {m i : ℕ} (hi : i ≤ m) (y : V) :
    ‖iteratedFDeriv ℝ i (fun x => Complex.exp (L x + κ) - 1) y‖ ≤ τ * (A + 1) ^ (m + 1) * (1 + ‖y‖) := by
  have hR : 1 ≤ A + 1 := by linarith
  have hc : ContDiff ℝ ⊤ (fun x => Complex.exp (L x + κ)) := (L.contDiff.add contDiff_const).cexp
  have h1 : ‖Complex.exp (L y + κ)‖ = 1 := by
    rw [Complex.norm_exp, hre, Real.exp_zero]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [norm_iteratedFDeriv_zero]
    refine (norm_cexp_sub_one_le_of_re_eq_zero _ (hre y)).trans ?_
    calc ‖L y + κ‖ ≤ ‖L‖ * ‖y‖ + ‖κ‖ := (norm_add_le _ _).trans (by gcongr; exact L.le_opNorm y)
      _ ≤ τ * A * ‖y‖ + τ * A := by gcongr
      _ = τ * A * (1 + ‖y‖) := by ring
      _ ≤ τ * (A + 1) ^ (m + 1) * (1 + ‖y‖) := by
        gcongr
        calc A ≤ A + 1 := by linarith
          _ = (A + 1) ^ 1 := (pow_one _).symm
          _ ≤ (A + 1) ^ (m + 1) := pow_le_pow_right₀ hR (by omega)
  · rw [fun_iteratedFDeriv_sub_apply (hc.of_le (by exact_mod_cast le_top)).contDiffAt contDiffAt_const,
      iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, sub_zero]
    refine (norm_iteratedFDeriv_cexp_affine L κ i y).trans ?_
    rw [h1, mul_one]
    calc ‖L‖ ^ i ≤ (τ * A) ^ i := by gcongr
      _ = τ ^ i * A ^ i := mul_pow _ _ _
      _ ≤ τ * (A + 1) ^ (m + 1) * 1 := by
        rw [mul_one]
        gcongr
        · exact pow_le_of_le_one hτ0 hτ1 (by omega)
        · calc A ^ i ≤ (A + 1) ^ i := by gcongr; linarith
            _ ≤ (A + 1) ^ (m + 1) := pow_le_pow_right₀ hR (by omega)
      _ ≤ τ * (A + 1) ^ (m + 1) * (1 + ‖y‖) := by gcongr; linarith [norm_nonneg y]

theorem mul_translate_le (h : 𝓢(V, ℂ)) (L : V →L[ℝ] ℂ) (κ : ℂ) (hre : ∀ x, (L x + κ).re = 0)
    {τ A : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hA : 0 ≤ A) (hL : ‖L‖ ≤ τ * A) (hκ : ‖κ‖ ≤ τ * A)
    (c : V) (k m : ℕ) (y : V) :
    (1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ m (fun x => (Complex.exp (L x + κ) - 1) * h (x + c)) y‖ ≤
      τ * ((A + 1) ^ (m + 1) * 2 ^ m * (1 + ‖c‖) ^ (k + 1) * 2 ^ (k + 1) *
        (Finset.Iic (k + 1, m)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℂ p.1 p.2) h) := by
  set S := (Finset.Iic (k + 1, m)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℂ p.1 p.2) h
  have hS : 0 ≤ S := apply_nonneg _ _
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (h : V → ℂ) := h.smooth ⊤
  have hsc : ContDiff ℝ (⊤ : ℕ∞) (fun x => h (x + c)) := hsm.comp (contDiff_id.add contDiff_const)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun x => Complex.exp (L x + κ) - 1) :=
    ((L.contDiff.add contDiff_const).cexp).sub contDiff_const
  have hleib := norm_iteratedFDeriv_mul_le hχ hsc y (n := m) (by exact_mod_cast le_top)
  have hyc : 1 + ‖y‖ ≤ (1 + ‖c‖) * (1 + ‖y + c‖) := by
    have : ‖y‖ ≤ ‖y + c‖ + ‖c‖ := by
      calc ‖y‖ = ‖(y + c) - c‖ := by simp
        _ ≤ _ := norm_sub_le _ _
    nlinarith [norm_nonneg (y + c), norm_nonneg c]
  calc (1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ m (fun x => (Complex.exp (L x + κ) - 1) * h (x + c)) y‖
      ≤ (1 + ‖y‖) ^ k * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x => Complex.exp (L x + κ) - 1) y‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun x => h (x + c)) y‖ := by gcongr
    _ = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          (‖iteratedFDeriv ℝ i (fun x => Complex.exp (L x + κ) - 1) y‖ *
          ((1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ (m - i) h (y + c)‖)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [iteratedFDeriv_comp_add_right]; ring
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          (τ * ((A + 1) ^ (m + 1) * (1 + ‖c‖) ^ (k + 1) * 2 ^ (k + 1) * S)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hD := norm_iteratedFDeriv_cexp_sub_one_le L κ hre hτ0 hτ1 hA hL hκ him y
        have hj : (1 + ‖y + c‖) ^ (k + 1) * ‖iteratedFDeriv ℝ (m - i) h (y + c)‖ ≤ 2 ^ (k + 1) * S :=
          SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + 1, m)) le_rfl (Nat.sub_le _ _) h (y + c)
        calc ‖iteratedFDeriv ℝ i (fun x => Complex.exp (L x + κ) - 1) y‖ *
              ((1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ (m - i) h (y + c)‖)
            ≤ (τ * (A + 1) ^ (m + 1) * (1 + ‖y‖)) *
              ((1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ (m - i) h (y + c)‖) := by gcongr
          _ = τ * (A + 1) ^ (m + 1) * ((1 + ‖y‖) ^ (k + 1) * ‖iteratedFDeriv ℝ (m - i) h (y + c)‖) := by ring
          _ ≤ τ * (A + 1) ^ (m + 1) * (((1 + ‖c‖) * (1 + ‖y + c‖)) ^ (k + 1) *
                ‖iteratedFDeriv ℝ (m - i) h (y + c)‖) := by gcongr
          _ = τ * (A + 1) ^ (m + 1) * (1 + ‖c‖) ^ (k + 1) *
                ((1 + ‖y + c‖) ^ (k + 1) * ‖iteratedFDeriv ℝ (m - i) h (y + c)‖) := by rw [mul_pow]; ring
          _ ≤ τ * (A + 1) ^ (m + 1) * (1 + ‖c‖) ^ (k + 1) * (2 ^ (k + 1) * S) := by gcongr
          _ = τ * ((A + 1) ^ (m + 1) * (1 + ‖c‖) ^ (k + 1) * 2 ^ (k + 1) * S) := by ring
    _ = τ * ((A + 1) ^ (m + 1) * 2 ^ m * (1 + ‖c‖) ^ (k + 1) * 2 ^ (k + 1) * S) := by
        rw [← Finset.sum_mul]
        have := Nat.sum_range_choose m
        have e : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) = 2 ^ m := by exact_mod_cast this
        rw [e]; ring

variable [FiniteDimensional ℝ V]

def pairL {P : V → V → ℝ} (hP : IsPairing P) (b : V) : V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => P y b
      map_add' := fun x x' => hP.addL x x' b
      map_smul' := fun c y => hP.smulL c y b }

@[simp] theorem pairL_apply {P : V → V → ℝ} (hP : IsPairing P) (b y : V) : pairL hP b y = P y b := rfl

theorem seminorm_schrF_sub_le {P : V → V → ℝ} (hP : IsPairing P) (u : V × V) (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ 1 → ∀ h g : 𝓢(V, ℂ), ⇑g = schrF P (t • u) ⇑h →
      SchwartzMap.seminorm ℂ k m (g - h) ≤
        C * |t| * (Finset.Iic (k + 1, m + 1)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℂ p.1 p.2) h := by
  obtain ⟨a, b⟩ := u
  set ℓ := pairL hP b
  set c₀ := P a b
  set A : ℝ := 2 * Real.pi * (‖ℓ‖ + |c₀|) with hAdef
  have hA : 0 ≤ A := by positivity
  set C₁ : ℝ := (A + 1) ^ (m + 1) * 2 ^ m * (1 + ‖a‖) ^ (k + 1) * 2 ^ (k + 1)
  set C₂ : ℝ := 2 ^ k * (1 + ‖a‖) ^ k * ‖a‖
  refine ⟨C₁ + C₂, by positivity, fun t ht h g hg => ?_⟩
  set S := (Finset.Iic (k + 1, m + 1)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℂ p.1 p.2) h
  have hS : 0 ≤ S := apply_nonneg _ _
  have hS1 : (Finset.Iic (k + 1, m)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℂ p.1 p.2) h ≤ S :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.Iic_subset_Iic.mpr (Prod.mk_le_mk.mpr ⟨by omega, by omega⟩))) h
  have hS2 : (Finset.Iic (k, m + 1)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℂ p.1 p.2) h ≤ S :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.Iic_subset_Iic.mpr (Prod.mk_le_mk.mpr ⟨by omega, by omega⟩))) h
  set L : V →L[ℝ] ℂ := ℓ.smulRight (-(2 * Real.pi * Complex.I) * (t : ℂ))
  set κ : ℂ := -(2 * Real.pi * Complex.I) * ((t ^ 2 * c₀ / 2 : ℝ) : ℂ)
  have hLκ : ∀ x, L x + κ = -(2 * Real.pi * Complex.I) * ((t * P x b + t ^ 2 * c₀ / 2 : ℝ) : ℂ) := by
    intro x
    simp only [L, κ, ContinuousLinearMap.smulRight_apply, pairL_apply, ℓ, Complex.real_smul]
    push_cast; ring
  have hre : ∀ x, (L x + κ).re = 0 := by
    intro x; rw [hLκ]
    generalize (t * P x b + t ^ 2 * c₀ / 2 : ℝ) = r
    simp [Complex.mul_re]
  have hτ0 : 0 ≤ |t| := abs_nonneg t
  have hLn : ‖L‖ ≤ |t| * A := by
    simp only [L, ContinuousLinearMap.norm_smulRight_apply, norm_mul, norm_neg, Complex.norm_real,
      Complex.norm_I, Complex.norm_ofNat, Real.norm_eq_abs, hAdef]
    rw [abs_of_pos Real.pi_pos]
    have := mul_nonneg (mul_nonneg hτ0 Real.pi_pos.le) (abs_nonneg c₀)
    nlinarith [norm_nonneg ℓ, Real.pi_pos]
  have hκn : ‖κ‖ ≤ |t| * A := by
    simp only [κ, norm_mul, norm_neg, Complex.norm_real, Complex.norm_I, Complex.norm_ofNat,
      Real.norm_eq_abs, hAdef]
    rw [abs_of_pos Real.pi_pos]
    have ht2 : |t ^ 2 * c₀ / 2| ≤ |t| * |c₀| := by
      rw [abs_div, abs_mul, abs_pow, abs_two]
      have : |t| ^ 2 ≤ |t| := by nlinarith
      have : 0 ≤ |c₀| := abs_nonneg _
      nlinarith
    have h3 := mul_le_mul_of_nonneg_left ht2 (by positivity : (0:ℝ) ≤ 2 * Real.pi)
    have h4 := mul_nonneg (mul_nonneg hτ0 Real.pi_pos.le) (norm_nonneg ℓ)
    nlinarith
  have hgfun : ((g - h : 𝓢(V, ℂ)) : V → ℂ) =
      (fun x => (Complex.exp (L x + κ) - 1) * h (x + t • a)) + (fun x => h (x + t • a) - h x) := by
    funext x
    simp only [SchwartzMap.sub_apply, Pi.add_apply, hg, schrF, Prod.smul_fst, Prod.smul_snd,
      hP.smulR, hP.smulL, hLκ, c₀]
    push_cast; ring_nf
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (h : V → ℂ) := h.smooth ⊤
  have hsc : ContDiff ℝ (⊤ : ℕ∞) (fun x => h (x + t • a)) := hsm.comp (contDiff_id.add contDiff_const)
  have hc1 : ContDiff ℝ (⊤ : ℕ∞) (fun x => (Complex.exp (L x + κ) - 1) * h (x + t • a)) :=
    (((L.contDiff.add contDiff_const).cexp).sub contDiff_const).mul hsc
  have hc2 : ContDiff ℝ (⊤ : ℕ∞) (fun x => h (x + t • a) - h x) := hsc.sub hsm
  have hta : ‖t • a‖ ≤ ‖a‖ := by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) ht
  refine SchwartzMap.seminorm_le_bound ℂ k m _ (by positivity) fun y => ?_
  rw [hgfun, iteratedFDeriv_add_apply (hc1.of_le (by exact_mod_cast le_top)).contDiffAt
    (hc2.of_le (by exact_mod_cast le_top)).contDiffAt]
  have e1 := mul_translate_le h L κ hre hτ0 ht hA hLn hκn (t • a) k m y
  have e2 := translate_sub_le h (t • a) k m y
  have hy : ‖y‖ ^ k ≤ (1 + ‖y‖) ^ k := by gcongr; linarith
  calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => (Complex.exp (L x + κ) - 1) * h (x + t • a)) y +
        iteratedFDeriv ℝ m (fun x => h (x + t • a) - h x) y‖
      ≤ (1 + ‖y‖) ^ k * (‖iteratedFDeriv ℝ m (fun x => (Complex.exp (L x + κ) - 1) * h (x + t • a)) y‖ +
        ‖iteratedFDeriv ℝ m (fun x => h (x + t • a) - h x) y‖) := by
        gcongr
        · exact norm_add_le _ _
    _ = (1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ m (fun x => (Complex.exp (L x + κ) - 1) * h (x + t • a)) y‖ +
        (1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ m (fun x => h (x + t • a) - h x) y‖ := mul_add _ _ _
    _ ≤ |t| * ((A + 1) ^ (m + 1) * 2 ^ m * (1 + ‖t • a‖) ^ (k + 1) * 2 ^ (k + 1) *
          (Finset.Iic (k + 1, m)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℂ p.1 p.2) h) +
        2 ^ k * (1 + ‖t • a‖) ^ k * ‖t • a‖ *
          (Finset.Iic (k, m + 1)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℂ p.1 p.2) h := add_le_add e1 e2
    _ ≤ |t| * (C₁ * S) + 2 ^ k * (1 + ‖a‖) ^ k * (|t| * ‖a‖) * S := by
        have hX : (A + 1) ^ (m + 1) * 2 ^ m * (1 + ‖t • a‖) ^ (k + 1) * 2 ^ (k + 1) ≤ C₁ := by
          simp only [C₁]; gcongr
        refine add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul hX hS1 (apply_nonneg _ _) (by positivity)) hτ0) ?_
        rw [norm_smul, Real.norm_eq_abs] at hta ⊢
        gcongr
    _ = (C₁ + C₂) * |t| * S := by simp only [C₂]; ring

theorem schrF_sub_seminorm_le_abs : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ (u : V × V) (s₀ : Finset (ℕ × ℕ)),
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (t : ℝ), |t| ≤ 1 → ∀ (h g : 𝓢(V, ℂ)),
      ⇑g = GlobalTheory.ArchUniq.schrF P (t • u) ⇑h →
        (s₀.sup (schwartzSeminormFamily ℂ V ℂ)) (g - h) ≤ C * |t| * (s.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
  intro V _ _ _ P hP u s₀
  choose C hC0 hC using fun p : ℕ × ℕ => seminorm_schrF_sub_le hP u p.1 p.2
  refine ⟨Finset.Iic (s₀.sup Prod.fst + 1, s₀.sup Prod.snd + 1), ∑ p ∈ s₀, C p,
    Finset.sum_nonneg fun p _ => hC0 p, fun t ht h g hg => ?_⟩
  have hsum0 : 0 ≤ ∑ p ∈ s₀, C p := Finset.sum_nonneg fun p _ => hC0 p
  refine Seminorm.finset_sup_apply_le (mul_nonneg (mul_nonneg hsum0 (abs_nonneg t)) (apply_nonneg _ _))
    fun p hp => ?_
  have hsub : Finset.Iic (p.1 + 1, p.2 + 1) ⊆ Finset.Iic (s₀.sup Prod.fst + 1, s₀.sup Prod.snd + 1) :=
    Finset.Iic_subset_Iic.mpr (Prod.mk_le_mk.mpr
      ⟨Nat.add_le_add_right (Finset.le_sup (f := Prod.fst) hp) 1,
       Nat.add_le_add_right (Finset.le_sup (f := Prod.snd) hp) 1⟩)
  have hmono : (Finset.Iic (p.1 + 1, p.2 + 1)).sup (schwartzSeminormFamily ℂ V ℂ) h ≤
      (Finset.Iic (s₀.sup Prod.fst + 1, s₀.sup Prod.snd + 1)).sup (schwartzSeminormFamily ℂ V ℂ) h :=
    Seminorm.le_def.mp (Finset.sup_mono hsub) h
  have hCp : C p ≤ ∑ q ∈ s₀, C q := Finset.single_le_sum (fun q _ => hC0 q) hp
  calc schwartzSeminormFamily ℂ V ℂ p (g - h) = SchwartzMap.seminorm ℂ p.1 p.2 (g - h) := rfl
    _ ≤ C p * |t| * (Finset.Iic (p.1 + 1, p.2 + 1)).sup (schwartzSeminormFamily ℂ V ℂ) h := hC p t ht h g hg
    _ ≤ (∑ q ∈ s₀, C q) * |t| *
        (Finset.Iic (s₀.sup Prod.fst + 1, s₀.sup Prod.snd + 1)).sup (schwartzSeminormFamily ℂ V ℂ) h := by
      gcongr

end GlobalTheory.ArchUniq.SchrLip
