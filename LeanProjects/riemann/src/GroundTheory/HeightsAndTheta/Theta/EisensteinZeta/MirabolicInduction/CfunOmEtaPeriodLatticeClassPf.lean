import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmStatements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open UpperHalfPlane ModularGroup ModularForm Complex
open scoped Real Modular MatrixGroups

namespace EtaPeriodLatticeClass

theorem discriminant_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.discriminant (γ • τ) = denom γ τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
  have h := congr_fun
    (SlashInvariantForm.slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant γ) τ
  rw [SL_slash_apply] at h
  have hd : denom γ τ ≠ 0 := denom_ne_zero γ τ
  rw [← h, mul_comm (ModularForm.discriminant (γ • τ)), ← mul_assoc, ← zpow_add₀ hd]
  simp

theorem norm_eta_smul_pow_four (γ : SL(2, ℤ)) (τ : ℍ) :
    ‖η ((γ • τ : ℍ) : ℂ)‖ ^ 4 = ‖denom γ τ‖ ^ 2 * ‖η (τ : ℂ)‖ ^ 4 := by
  have h := congr_arg norm (discriminant_smul γ τ)
  simp only [ModularForm.discriminant, norm_mul, norm_pow, norm_zpow] at h
  have h6 : (‖η ((γ • τ : ℍ) : ℂ)‖ ^ 4) ^ 6 = (‖denom γ τ‖ ^ 2 * ‖η (τ : ℂ)‖ ^ 4) ^ 6 := by
    rw [← pow_mul, mul_pow, ← pow_mul, ← pow_mul]
    rw [show (4 : ℕ) * 6 = 24 from rfl, show (2 : ℕ) * 6 = 12 from rfl, h]
    norm_cast
  exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).mp h6

theorem etaPeriod_smul (γ : SL(2, ℤ)) (τ : ℍ) : etaPeriod (γ • τ) = etaPeriod τ := by
  unfold etaPeriod
  rw [norm_eta_smul_pow_four, ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
  have : ‖denom γ τ‖ ≠ 0 := norm_ne_zero_iff.mpr (denom_ne_zero γ τ)
  field_simp

theorem mem_latticeOf {τ z : ℂ} : z ∈ latticeOf τ ↔ ∃ m n : ℤ, z = m + n * τ := by
  unfold latticeOf
  rw [SetLike.mem_coe, Submodule.mem_span_pair]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp [zsmul_eq_mul]⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp [zsmul_eq_mul]⟩

theorem coord_unique {τ : ℍ} {m n m' n' : ℤ}
    (h : (m : ℂ) + n * (τ : ℂ) = m' + n' * (τ : ℂ)) : m = m' ∧ n = n' := by
  have him := congr_arg Complex.im h
  have hre := congr_arg Complex.re h
  simp at him hre
  have hn : n = n' := by
    rcases him with h | h
    · exact_mod_cast h
    · exact absurd h τ.im_pos.ne'
  subst hn
  refine ⟨?_, rfl⟩
  exact_mod_cast (by linarith : (m : ℝ) = m')

theorem exists_SL_smul_eq {τ τ' : ℍ} {μ : ℂ} (hμ : μ ≠ 0)
    (h1 : ∀ z ∈ latticeOf (τ : ℂ), μ * z ∈ latticeOf (τ' : ℂ))
    (h2 : ∀ w ∈ latticeOf (τ' : ℂ), μ⁻¹ * w ∈ latticeOf (τ : ℂ)) :
    ∃ γ : SL(2, ℤ), γ • τ = τ' := by

  obtain ⟨d, c, hdc⟩ := mem_latticeOf.mp (h2 1 (mem_latticeOf.mpr ⟨1, 0, by simp⟩))
  obtain ⟨b, a, hba⟩ := mem_latticeOf.mp (h2 τ' (mem_latticeOf.mpr ⟨0, 1, by simp⟩))

  obtain ⟨h, g, hhg⟩ := mem_latticeOf.mp (h1 1 (mem_latticeOf.mpr ⟨1, 0, by simp⟩))
  obtain ⟨f, e, hfe⟩ := mem_latticeOf.mp (h1 τ (mem_latticeOf.mpr ⟨0, 1, by simp⟩))
  rw [mul_one] at hdc hhg

  have k1 : ((d * h + c * f : ℤ) : ℂ) + ((d * g + c * e : ℤ) : ℂ) * (τ' : ℂ) =
      ((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * (τ' : ℂ) := by
    have hinv : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ
    push_cast
    linear_combination hinv - μ * hdc - (d : ℂ) * hhg - (c : ℂ) * hfe
  have k2 : ((b * h + a * f : ℤ) : ℂ) + ((b * g + a * e : ℤ) : ℂ) * (τ' : ℂ) =
      ((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * (τ' : ℂ) := by
    have hinv : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ
    push_cast
    linear_combination (τ' : ℂ) * hinv - μ * hba - (b : ℂ) * hhg - (a : ℂ) * hfe
  obtain ⟨E4, E3⟩ := coord_unique k1
  obtain ⟨E2, E1⟩ := coord_unique k2
  have hdet1 : (a * d - b * c) * (e * h - f * g) = 1 := by
    linear_combination (c * f + d * h) * E1 + E4 - (c * e + d * g) * E2

  have hw : (c : ℂ) * τ + d ≠ 0 := by
    rw [add_comm, ← hdc]; exact inv_ne_zero hμ
  have hτ' : (τ' : ℂ) = ((a : ℂ) * τ + b) / ((c : ℂ) * τ + d) := by
    rw [eq_div_iff hw, add_comm ((c : ℂ) * τ), ← hdc, add_comm ((a : ℂ) * τ), ← hba]
    field_simp

  have hdetpos : 0 < a * d - b * c := by
    have him := congr_arg Complex.im hτ'
    rw [Complex.div_im] at him
    have hN : 0 < Complex.normSq ((c : ℂ) * τ + d) := Complex.normSq_pos.mpr hw
    have key : (τ' : ℂ).im * Complex.normSq ((c : ℂ) * τ + d) = ((a * d - b * c : ℤ) : ℝ) * τ.im := by
      rw [him, sub_mul, div_mul_cancel₀ _ hN.ne', div_mul_cancel₀ _ hN.ne']
      simp
      ring
    have : (0 : ℝ) < ((a * d - b * c : ℤ) : ℝ) * τ.im := by
      rw [← key]; exact mul_pos τ'.im_pos hN
    have := (pos_of_mul_pos_left this τ.im_pos.le)
    exact_mod_cast this
  have hdet : a * d - b * c = 1 :=
    Int.eq_one_of_mul_eq_one_right hdetpos.le hdet1
  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact hdet⟩
  refine ⟨γ, UpperHalfPlane.ext ?_⟩
  rw [coe_specialLinearGroup_apply, hτ']
  simp [γ]

theorem of_EtaPeriodModularInvariant (hinv : EtaPeriodModularInvariant.Statement) :
    EtaPeriodLatticeClass.Statement := by
  rintro Λ τ τ' ⟨c, hc, hΛ⟩ ⟨c', hc', hΛ'⟩
  have h1 : ∀ z ∈ latticeOf (τ : ℂ), c' / c * z ∈ latticeOf (τ' : ℂ) := by
    intro z hz
    rw [← hΛ] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [← hΛ']
    exact ⟨x, hx, by field_simp⟩
  have h2 : ∀ w ∈ latticeOf (τ' : ℂ), (c' / c)⁻¹ * w ∈ latticeOf (τ : ℂ) := by
    intro w hw
    rw [← hΛ'] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    rw [← hΛ]
    exact ⟨x, hx, by field_simp⟩
  obtain ⟨γ, hγ⟩ := exists_SL_smul_eq (div_ne_zero hc' hc) h1 h2
  rw [← hγ, hinv]

theorem proof : EtaPeriodLatticeClass.Statement :=
  of_EtaPeriodModularInvariant etaPeriod_smul

end EtaPeriodLatticeClass

example : etaPeriod (ModularGroup.T • UpperHalfPlane.I) = etaPeriod UpperHalfPlane.I :=
  EtaPeriodLatticeClass.etaPeriod_smul _ _

end GroundTheory.Heights₂.Theta
