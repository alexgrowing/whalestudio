import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerSlashInverseCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGammaOneOfCoeffSeq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1CharElementary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspidalAtAllCuspsSL2SlashIntMatrix
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.AtkinLehnerForm

theorem toGL_entry (A : M2) (hA : A.det ≠ 0) (i j : Fin 2) :
    (↑(GlobalTheory.HeckeFamilyMatrices.toGL A) : Matrix (Fin 2) (Fin 2) ℝ) i j = (A i j : ℝ) := by
  rw [GlobalTheory.HeckeFamilyMatrices.toGL_val A hA]; simp

theorem slz_eq_slash (k : ℕ) (hk : 1 ≤ k) (δ : M2) (hδ : 0 < δ.det) (f : ℍ → ℂ) :
    slz k δ f = f ∣[(k : ℤ)] GlobalTheory.HeckeFamilyMatrices.toGL δ := by
  funext τ
  have hd : 0 < (GlobalTheory.HeckeFamilyMatrices.toGL δ).det.val := GlobalTheory.HeckeFamilyMatrices.toGL_det_pos δ hδ
  have hpt : ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)))
      = GlobalTheory.HeckeFamilyMatrices.toGL δ • τ := by
    ext1
    rw [slzMob_coe δ hδ τ, UpperHalfPlane.coe_smul_of_det_pos hd]
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, toGL_entry δ hδ.ne']
  rw [ModularForm.slash_apply, GlobalTheory.HeckeFamilyMatrices.sigma_pos hd, slz, hpt]
  have hdet : (GlobalTheory.HeckeFamilyMatrices.toGL δ).det.val = (δ.det : ℝ) := GlobalTheory.HeckeFamilyMatrices.toGL_det δ hδ.ne'
  rw [hdet, abs_of_pos (by exact_mod_cast hδ)]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e1 : (((m + 1 : ℕ) : ℤ) - 1) = ((m : ℕ) : ℤ) := by push_cast; ring
  rw [e1, zpow_natCast, zpow_neg, zpow_natCast]
  simp only [Nat.add_sub_cancel, UpperHalfPlane.denom, toGL_entry δ hδ.ne', Complex.ofReal_intCast]
  ring

end GlobalTheory.EisM.AtkinLehnerForm

namespace GlobalTheory.EisM.AtkinLehnerForm

theorem qs_add_int (a : ℕ → ℂ) (τ : ℍ) (m : ℤ) : qs a (ofComplex ((τ : ℂ) + m)) = qs a τ := by
  have him : 0 < ((τ : ℂ) + m).im := by simpa using τ.im_pos
  have hcoe : ((ofComplex ((τ : ℂ) + m) : ℍ) : ℂ) = (τ : ℂ) + m := by
    rw [ofComplex_apply_of_im_pos him]
  simp only [qs, hcoe]
  congr 1
  funext n
  have e : cexp (2 * π * Complex.I * n * ((τ : ℂ) + m)) = cexp (2 * π * Complex.I * n * τ) := by
    rw [show 2 * π * Complex.I * n * ((τ : ℂ) + m) = 2 * π * Complex.I * n * τ + ((n * m : ℤ) : ℂ) * (2 * π * Complex.I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [e]

theorem slz_levelOne (k : ℕ) (a : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ) (h : a₀ * d₀ = 1) :
    slz k !![((1 : ℕ) : ℤ) * a₀, b₀; ((1 : ℕ) : ℤ) * ((0 : ℕ) : ℤ) * c₀, ((1 : ℕ) : ℤ) * d₀] (qs a)
      = fun τ => ((d₀ : ℂ) ^ k)⁻¹ * qs a τ := by
  funext τ
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e : (((((1 : ℕ) : ℤ) * 1 : ℤ) : ℂ) * (τ : ℂ) + ((b₀ : ℤ) : ℂ)) / (((((1 : ℕ) : ℤ) * ((0 : ℕ) : ℤ) * c₀ : ℤ) : ℂ) * (τ : ℂ) + ((((1 : ℕ) : ℤ) * 1 : ℤ) : ℂ))
        = (τ : ℂ) + ((b₀ : ℤ) : ℂ) := by push_cast; ring
    simp only [slz, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.det_fin_two_of, e, qs_add_int]
    push_cast
    try simp
  · have e : (((((1 : ℕ) : ℤ) * (-1) : ℤ) : ℂ) * (τ : ℂ) + ((b₀ : ℤ) : ℂ)) / (((((1 : ℕ) : ℤ) * ((0 : ℕ) : ℤ) * c₀ : ℤ) : ℂ) * (τ : ℂ) + ((((1 : ℕ) : ℤ) * (-1) : ℤ) : ℂ))
        = (τ : ℂ) + ((-b₀ : ℤ) : ℂ) := by push_cast; ring
    simp only [slz, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.det_fin_two_of, e, qs_add_int]
    push_cast
    try simp

end GlobalTheory.EisM.AtkinLehnerForm

open GlobalTheory.EisM.AtkinLehnerForm in

theorem GlobalTheory.EisM.atkinLehner_MF : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → MF k (N * l) (ch χ) a → ∃ a' : ℕ → ℂ, MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) := by
  intro k N l χ a a₀ b₀ c₀ d₀ h hk hN ha
  have hinv := GlobalTheory.T.atkinLehner_slash_inverse_character k N l χ (qs a) a₀ b₀ c₀ d₀ h hk hN ha.2
  suffices hex : ∃ a' : ℕ → ℂ, PolyB a' ∧ qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) by
    obtain ⟨a', h1, h2⟩ := hex
    exact ⟨a', ⟨h1, h2 ▸ hinv⟩, h2⟩
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have h' : (N : ℤ) * (a₀ * d₀) = 1 := by linear_combination h
    have hN1 : N = 1 := by exact_mod_cast Int.eq_one_of_mul_eq_one_right (by positivity) h'
    subst hN1
    have had : a₀ * d₀ = 1 := by simpa using h'
    rw [slz_levelOne k a a₀ b₀ c₀ d₀ had]
    obtain ⟨C, A, hC⟩ := ha.1
    refine ⟨fun n => ((d₀ : ℂ) ^ k)⁻¹ * a n, ⟨‖((d₀ : ℂ) ^ k)⁻¹‖ * C, A, fun n => ?_⟩, ?_⟩
    · rw [norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)
    · funext τ
      simp only [qs]
      rw [← tsum_mul_left]
      congr 1
      funext n
      ring
  · set δ : M2 := !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] with hδdef
    have hdet : δ.det = N := by rw [hδdef, Matrix.det_fin_two_of]; linear_combination (N : ℤ) * h
    have hδ : 0 < δ.det := by rw [hdet]; exact_mod_cast hN
    have hL : 0 < N * l := Nat.mul_pos hN hl
    haveI : NeZero (N * l) := ⟨hL.ne'⟩
    obtain ⟨f, hf⟩ := GlobalTheory.EisM.modularForm_gammaOne_of_MF k (N * l) N χ a hL (dvd_mul_right N l) ha
    have hF : slz k δ (qs a) = ⇑f ∣[(k : ℤ)] GlobalTheory.HeckeFamilyMatrices.toGL δ := by rw [hf]; exact slz_eq_slash k hk δ hδ _
    let F : ModularForm (Gamma1 (N * l)) (k : ℤ) :=
      { toFun := slz k δ (qs a)
        slash_action_eq' := by
          rintro _ ⟨A, (hA : A ∈ Gamma1 (N * l)), rfl⟩
          exact GlobalTheory.EisM.OnGammaOne.slash_inv (dvd_mul_right N l) hinv A hA
        holo' := by
          show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (slz k δ (qs a))
          rw [hF]; exact (ModularFormClass.holo f).slash _ _
        bdd_at_cusps' := by
          intro c hc
          show c.IsBoundedAt (slz k δ (qs a)) (k : ℤ)
          rw [hF, ← OnePoint.IsBoundedAt.smul_iff]
          apply ModularFormClass.bdd_at_cusps f
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
          exact GlobalTheory.HeckeFamilyMatrices.isCusp_SL2Z_toGL_smul δ hδ.ne' hc }
    refine ⟨coef F, ?_, qs_coef_of_mfc F⟩
    have hb := ModularFormClass.qExpansion_isBigO (Int.natCast_nonneg k) F
    simp only [strictWidthInfty_Gamma1, zpow_natCast] at hb
    exact polyB_of_isBigO hb
