import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.TranslateSpanLeCuspForms

open NumberField Matrix CongruenceSubgroup ModularForm Complex
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Real

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N] {k : ℤ}

omit [NeZero N] in
theorem one_mem_strictPeriods_Gamma0 :
    (1 : ℝ) ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, ?_, ?_⟩
  · change ModularGroup.T ∈ Gamma0 N
    rw [Gamma0_mem]
    simp [ModularGroup.T]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (change ((ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) _ _ : ℝ) = _
       simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom])

variable (p : ℕ) [NeZero p]

theorem slash_classicalUpper_apply (f : ℍ → ℂ) (j : ℤ) (τ : ℍ) :
    (f ∣[k] toReal (classicalUpper p j)) τ =
      (p : ℂ)⁻¹ * f (toReal (classicalUpper p j) • τ) := by
  have hdet := det_toReal_classicalUpper p j
  have hpos : 0 < (toReal (classicalUpper p j)).det.val := by rw [hdet]; exact natCast_pos_real p
  rw [slash_apply, σ_of_det_pos hpos, hdet]
  have hden : denom (toReal (classicalUpper p j)) τ = p := by
    simp [denom, toReal_apply, coe_classicalUpper]
  rw [hden]
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
  simp only [abs_of_pos (natCast_pos_real p)]
  push_cast
  rw [_root_.zpow_neg, zpow_sub_one₀ hp]
  field_simp

theorem coe_classicalUpper_smul (j : ℤ) (τ : ℍ) :
    ((toReal (classicalUpper p j) • τ : ℍ) : ℂ) = (τ + j) / p := by
  have hdet := det_toReal_classicalUpper p j
  have hpos : 0 < (toReal (classicalUpper p j)).det.val := by rw [hdet]; exact natCast_pos_real p
  rw [UpperHalfPlane.coe_smul_of_det_pos hpos]
  simp [num, denom, toReal_apply, coe_classicalUpper]

theorem slash_heckeAlpha_apply (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] toReal (heckeAlpha p)) τ = (p : ℂ) ^ (k - 1) * f (toReal (heckeAlpha p) • τ) := by
  have hdet := det_toReal_heckeAlpha p
  have hpos : 0 < (toReal (heckeAlpha p)).det.val := by rw [hdet]; exact natCast_pos_real p
  rw [slash_apply, σ_of_det_pos hpos, hdet]
  have hden : denom (toReal (heckeAlpha p)) τ = 1 := by
    simp [denom, toReal_apply, heckeAlpha, coe_upperHecke]
  rw [hden, _root_.one_zpow, mul_one]
  simp only [abs_of_pos (natCast_pos_real p)]
  push_cast
  ring

theorem coe_heckeAlpha_smul (τ : ℍ) : ((toReal (heckeAlpha p) • τ : ℍ) : ℂ) = p * τ := by
  have hdet := det_toReal_heckeAlpha p
  have hpos : 0 < (toReal (heckeAlpha p)).det.val := by rw [hdet]; exact natCast_pos_real p
  rw [UpperHalfPlane.coe_smul_of_det_pos hpos]
  simp [num, denom, toReal_apply, heckeAlpha, coe_upperHecke]

theorem sum_exp_mul_div (m : ℕ) :
    ∑ j : Fin p, Complex.exp (2 * π * I * ((j : ℕ) * m : ℂ) / p) = if p ∣ m then (p : ℂ) else 0 := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
  set ζ : ℂ := Complex.exp (2 * π * I / p)
  have hζ : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p (NeZero.ne p)
  have e : ∀ j : ℕ, Complex.exp (2 * π * I * ((j : ℂ) * m) / p) = (ζ ^ m) ^ j := by
    intro j
    rw [← pow_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ m) ^ j) p]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).2 h]
    simp
  · have h1 : ζ ^ m ≠ 1 := fun h' => h ((hζ.pow_eq_one_iff_dvd m).1 h')
    rw [geom_sum_eq h1, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

local notation "𝕢₁" => Function.Periodic.qParam 1

theorem qParam_one_pow_smul_classicalUpper (j : ℕ) (τ : ℍ) (m : ℕ) :
    𝕢₁ ((toReal (classicalUpper p (j : ℤ)) • τ : ℍ) : ℂ) ^ m =
      Complex.exp (2 * π * I * (τ : ℂ) * m / p) * Complex.exp (2 * π * I * ((j : ℂ) * m) / p) := by
  rw [coe_classicalUpper_smul, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem qParam_one_pow_smul_heckeAlpha (τ : ℍ) (m : ℕ) :
    𝕢₁ ((toReal (heckeAlpha p) • τ : ℍ) : ℂ) ^ m = 𝕢₁ (τ : ℂ) ^ (m * p) := by
  rw [coe_heckeAlpha_smul, Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul,
    ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

def heckeCoeff (N p : ℕ) (k : ℤ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p) + if p ∣ N then 0 else if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0

variable [Fact p.Prime]

theorem hasSum_heckeCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (τ : ℍ) :
    HasSum (fun n => heckeCoeff N p k (fun m => (qExpansion 1 f).coeff m) n * 𝕢₁ (τ : ℂ) ^ n)
      (heckeCusp N p k f τ) := by
  set a : ℕ → ℂ := fun m => (qExpansion 1 f).coeff m
  have hf : ∀ z : ℍ, HasSum (fun m => a m * 𝕢₁ (z : ℂ) ^ m) (f z) := fun z =>
    ModularForm.hasSum_qExpansion f one_pos one_mem_strictPeriods_Gamma0 z
  have hpinj : Function.Injective fun n : ℕ => n * p := fun x y h =>
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (NeZero.ne p)) h

  have hU : HasSum (fun n => a (n * p) * 𝕢₁ (τ : ℂ) ^ n)
      (∑ j : Fin p, ((f : ℍ → ℂ) ∣[k] toReal (classicalUpper p ((j : ℕ) : ℤ))) τ) := by
    have h1 : HasSum (fun m => ∑ j : Fin p, (p : ℂ)⁻¹ *
        (a m * 𝕢₁ ((toReal (classicalUpper p ((j : ℕ) : ℤ)) • τ : ℍ) : ℂ) ^ m))
        (∑ j : Fin p, ((f : ℍ → ℂ) ∣[k] toReal (classicalUpper p ((j : ℕ) : ℤ))) τ) := by
      refine hasSum_sum fun j _ => ?_
      rw [slash_classicalUpper_apply]
      exact (hf _).mul_left _
    have h2 : (fun m => ∑ j : Fin p, (p : ℂ)⁻¹ *
        (a m * 𝕢₁ ((toReal (classicalUpper p ((j : ℕ) : ℤ)) • τ : ℍ) : ℂ) ^ m)) =
        fun m => if p ∣ m then a m * Complex.exp (2 * π * I * (τ : ℂ) * m / p) else 0 := by
      funext m
      simp_rw [qParam_one_pow_smul_classicalUpper]
      have : ∀ j : Fin p, (p : ℂ)⁻¹ * (a m * (Complex.exp (2 * π * I * (τ : ℂ) * m / p) *
          Complex.exp (2 * π * I * (((j : ℕ) : ℂ) * m) / p))) =
          ((p : ℂ)⁻¹ * a m * Complex.exp (2 * π * I * (τ : ℂ) * m / p)) *
            Complex.exp (2 * π * I * (((j : ℕ) : ℂ) * m) / p) := fun j => by ring
      simp_rw [this]
      rw [← Finset.mul_sum, sum_exp_mul_div]
      have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
      split_ifs
      · field_simp
      · simp
    rw [h2] at h1
    rw [← hpinj.hasSum_iff (fun m hm => by
      rw [if_neg]
      rintro ⟨c, rfl⟩
      exact hm ⟨c, mul_comm c p⟩)] at h1
    convert h1 using 1
    funext n
    simp only [Function.comp_apply, dvd_mul_left, if_true]
    congr 1
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
    push_cast
    field_simp

  have hL : HasSum (fun n => (if p ∣ N then 0 else if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0) *
      𝕢₁ (τ : ℂ) ^ n) ((if p ∣ N then 0 else (f : ℍ → ℂ) ∣[k] toReal (heckeAlpha p)) τ) := by
    split_ifs with hpN
    · simp
    · have h1 : HasSum (fun m => (p : ℂ) ^ (k - 1) * (a m * 𝕢₁ (τ : ℂ) ^ (m * p)))
          (((f : ℍ → ℂ) ∣[k] toReal (heckeAlpha p)) τ) := by
        rw [slash_heckeAlpha_apply]
        have := (hf (toReal (heckeAlpha p) • τ)).mul_left ((p : ℂ) ^ (k - 1))
        simpa only [qParam_one_pow_smul_heckeAlpha] using this
      rw [← hpinj.hasSum_iff (f := fun n => (if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0) *
          𝕢₁ (τ : ℂ) ^ n) (fun m hm => by
        rw [if_neg, zero_mul]
        rintro ⟨c, rfl⟩
        exact hm ⟨c, mul_comm c p⟩)]
      convert h1 using 1
      funext m
      simp only [Function.comp_apply, dvd_mul_left, if_true,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (NeZero.ne p))]
      ring
  have e1 : (fun n => heckeCoeff N p k a n * 𝕢₁ (τ : ℂ) ^ n) = fun n => a (n * p) * 𝕢₁ (τ : ℂ) ^ n +
      (if p ∣ N then 0 else if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0) * 𝕢₁ (τ : ℂ) ^ n := by
    funext n
    simp only [heckeCoeff]
    ring
  have e2 : heckeCusp N p k f τ = (∑ j : Fin p, ((f : ℍ → ℂ) ∣[k] toReal (classicalUpper p ((j : ℕ) : ℤ))) τ) +
      ((if p ∣ N then 0 else (f : ℍ → ℂ) ∣[k] toReal (heckeAlpha p)) τ) := by
    rw [coe_heckeCusp]
    unfold heckeOp
    rw [Pi.add_apply, Finset.sum_apply]
  rw [e1, e2]
  exact hU.add hL

theorem qExpansion_coeff_heckeCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) :
    (qExpansion 1 (heckeCusp N p k f)).coeff n =
      heckeCoeff N p k (fun m => (qExpansion 1 f).coeff m) n :=
  (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_Gamma0
    (f := heckeCusp N p k f) (fun τ => by simpa only [smul_eq_mul] using hasSum_heckeCusp p f τ) n).symm

theorem qExpansion_coeff_eq_of_hasSum (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) {b : ℕ → ℂ}
    (hb : ∀ τ : ℍ, HasSum (fun n => b n * 𝕢₁ (τ : ℂ) ^ n) (f τ)) (n : ℕ) :
    (qExpansion 1 f).coeff n = b n :=
  (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_Gamma0 (f := f)
    (fun τ => by simpa only [smul_eq_mul] using hb τ) n).symm

theorem hasSum_qExpansion_cusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (τ : ℍ) :
    HasSum (fun n => (qExpansion 1 f).coeff n * 𝕢₁ (τ : ℂ) ^ n) (f τ) :=
  ModularForm.hasSum_qExpansion f one_pos one_mem_strictPeriods_Gamma0 τ

theorem qExpansion_coeff_sub_smul (f g : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (c : ℂ) (n : ℕ) :
    (qExpansion 1 (⇑(g - c • f) : ℍ → ℂ)).coeff n = (qExpansion 1 g).coeff n - c * (qExpansion 1 f).coeff n := by
  refine qExpansion_coeff_eq_of_hasSum (g - c • f)
    (b := fun m => (qExpansion 1 g).coeff m - c * (qExpansion 1 f).coeff m) (fun τ => ?_) n
  have := (hasSum_qExpansion_cusp g τ).sub ((hasSum_qExpansion_cusp f τ).mul_left c)
  have e1 : (fun m => ((qExpansion 1 g).coeff m - c * (qExpansion 1 f).coeff m) * 𝕢₁ (τ : ℂ) ^ m) =
      fun m => (qExpansion 1 g).coeff m * 𝕢₁ (τ : ℂ) ^ m - c * ((qExpansion 1 f).coeff m * 𝕢₁ (τ : ℂ) ^ m) := by
    funext m
    ring
  have e2 : (g - c • f) τ = g τ - c * f τ := rfl
  rw [e1, e2]
  exact this

theorem eq_zero_of_qExpansion_coeff (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (h : ∀ n, (qExpansion 1 f).coeff n = 0) : f = 0 := by
  ext τ
  have := hasSum_qExpansion_cusp f τ
  simp only [h, zero_mul] at this
  rw [this.unique hasSum_zero]
  rfl

theorem eq_zero_of_eigen_of_coeff_one (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (ev : ℕ → ℂ)
    (hf : ∀ (p : ℕ) [Fact p.Prime], heckeCusp N p k f = ev p • f)
    (h1 : (qExpansion 1 f).coeff 1 = 0) : f = 0 := by
  refine eq_zero_of_qExpansion_coeff f fun n => ?_
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact CuspFormClass.qExpansion_coeff_zero f one_pos one_mem_strictPeriods_Gamma0
      · exact h1
    · set p := n.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have : Fact p.Prime := ⟨hp⟩
      have : NeZero p := ⟨hp.ne_zero⟩
      set m := n / p
      have hnm : n = m * p := (Nat.div_mul_cancel (Nat.minFac_dvd n)).symm
      have hm : m < n := Nat.div_lt_self (by omega) hp.one_lt
      have hmp : m / p < n := lt_of_le_of_lt (Nat.div_le_self m p) hm
      have key := qExpansion_coeff_heckeCusp p f m
      rw [hf p] at key
      have hsm : (qExpansion 1 (⇑(ev p • f) : ℍ → ℂ)).coeff m = ev p * (qExpansion 1 f).coeff m := by
        refine qExpansion_coeff_eq_of_hasSum (ev p • f) (b := fun j => ev p * (qExpansion 1 f).coeff j)
          (fun τ => ?_) m
        have := (hasSum_qExpansion_cusp f τ).mul_left (ev p)
        have e1 : (fun j => ev p * (qExpansion 1 f).coeff j * 𝕢₁ (τ : ℂ) ^ j) =
            fun j => ev p * ((qExpansion 1 f).coeff j * 𝕢₁ (τ : ℂ) ^ j) := by
          funext j
          ring
        have e2 : (ev p • f) τ = ev p * f τ := rfl
        rw [e1, e2]
        exact this
      rw [hsm, ih m hm, mul_zero] at key
      unfold heckeCoeff at key
      simp only at key
      rw [ih (m / p) hmp] at key
      simp only [mul_zero, ite_self, add_zero] at key
      rw [hnm]
      exact key.symm

theorem eq_smul_of_eigen (f g : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (ev : ℕ → ℂ)
    (hf : ∀ (p : ℕ) [Fact p.Prime], heckeCusp N p k f = ev p • f)
    (hg : ∀ (p : ℕ) [Fact p.Prime], heckeCusp N p k g = ev p • g)
    (hf1 : (qExpansion 1 f).coeff 1 = 1) : g = (qExpansion 1 g).coeff 1 • f := by
  set c := (qExpansion 1 g).coeff 1
  have h := eq_zero_of_eigen_of_coeff_one (g - c • f) ev (fun p _ => by
    rw [map_sub, map_smul, hf p, hg p, smul_sub, smul_comm])
    (by rw [qExpansion_coeff_sub_smul, hf1, mul_one, sub_self])
  exact sub_eq_zero.1 h

end GL2Classical

end

end GroundTheory.Automorphic
