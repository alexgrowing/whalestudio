import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblPair

section Cplx
variable {r : ℕ}

noncomputable def lin (G P x₁ x₂ : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  P * (G * x₂.map conj)ᵀ + (1 - P) * x₁⁻¹

noncomputable def anti (G P x₁ x₂ : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  P * (x₁ᵀ * G) + (1 - P) * x₂⁻¹.map conj

variable {G Gi P x₁ x₂ g₁ g₂ u₁ u₂ : Matrix (Fin r) (Fin r) ℂ} {c : ℂ}

theorem den_eq (h₁ h₂ q : Matrix (Fin r) (Fin r) ℂ) (hc : c ≠ 0) :
    ((2 * c)⁻¹ • (Gi * (h₁ - h₂))) * (c • ((1 - (2 : ℂ) • q) * G)) +
      (2 : ℂ)⁻¹ • (Gi * (h₁ + h₂) * G) = Gi * (h₂ * q + h₁ * (1 - q)) * G := by
  have e : (2 * c)⁻¹ * c = 2⁻¹ := by field_simp
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, e]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
    Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul]
  module

theorem num_eq (h₁ h₂ q : Matrix (Fin r) (Fin r) ℂ) :
    ((2 : ℂ)⁻¹ • (h₁ + h₂)) * (c • ((1 - (2 : ℂ) • q) * G)) + (c / 2) • ((h₁ - h₂) * G) =
      c • ((h₁ * (1 - q) - h₂ * q) * G) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
    Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul]
  module

theorem den'_eq (k₁ k₂ p : Matrix (Fin r) (Fin r) ℂ) (hc : c ≠ 0) :
    (c • (G * (1 - (2 : ℂ) • p))) * ((2 * -c)⁻¹ • ((k₁ - k₂) * Gi)) +
      (2 : ℂ)⁻¹ • (G * ((k₁ + k₂) * Gi)) = G * (p * k₁ + (1 - p) * k₂) * Gi := by
  have e : c * (2 * -c)⁻¹ = -2⁻¹ := by field_simp
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, e]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
    Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul]
  module

theorem map_conj_inv (h : g₁ * u₁ = 1) : g₁.map conj * u₁.map conj = 1 := by
  rw [← Matrix.map_mul, h]
  simp

theorem proj_parts (hP : P * P = P) (a b : Matrix (Fin r) (Fin r) ℂ) :
    P * (P * a + (1 - P) * b) = P * a ∧ (1 - P) * (P * a + (1 - P) * b) = (1 - P) * b := by
  constructor <;>
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hP,
    Matrix.mul_one, Matrix.one_mul] <;> abel

theorem lin_act (hP : P * P = P) (h₁ : g₁ * u₁ = 1) (h₂ : g₂ * u₂ = 1)
    (hg : g₂ᵀ * G * g₂.map conj = G) :
    lin G P (g₁ * x₁) (g₂ * x₂) = P * lin G P x₁ x₂ * u₂ + (1 - P) * lin G P x₁ x₂ * u₁ := by
  have e : G * g₂.map conj = u₂ᵀ * G := by
    calc _ = (g₂ * u₂)ᵀ * G * g₂.map conj := by rw [h₂]; simp
      _ = u₂ᵀ * (g₂ᵀ * G * g₂.map conj) := by simp only [transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hg]
  rw [lin, lin, (proj_parts hP _ _).1, (proj_parts hP _ _).2, Matrix.map_mul, ← Matrix.mul_assoc G,
    e, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv h₁]
  simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]

theorem anti_act (hP : P * P = P) (h₁ : g₁ * u₁ = 1) (h₂ : g₂ * u₂ = 1)
    (hg : g₁ᵀ * G * g₁.map conj = G) :
    anti G P (g₁ * x₁) (g₂ * x₂) =
      P * anti G P x₁ x₂ * u₁.map conj + (1 - P) * anti G P x₁ x₂ * u₂.map conj := by
  have e : g₁ᵀ * G = G * u₁.map conj := by
    calc _ = g₁ᵀ * G * (g₁.map conj * u₁.map conj) := by rw [map_conj_inv h₁, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hg]
  rw [anti, anti, (proj_parts hP _ _).1, (proj_parts hP _ _).2, transpose_mul,
    Matrix.mul_assoc x₁ᵀ, e, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv h₂, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem comm_proj (hP : P * P = P) (hPt : Pᵀ = P) (hG : G * Gi = 1) (hx₁ : x₁.det ≠ 0)
    (hx₂ : x₂.det ≠ 0) :
    anti G P x₁ x₂ * Gi * (lin G P x₁ x₂)ᵀ * P = P * (anti G P x₁ x₂ * Gi * (lin G P x₁ x₂)ᵀ) := by
  have hG' : Gi * G = 1 := mul_eq_one_comm.1 hG
  have e1 : x₁ᵀ * x₁⁻¹ᵀ = 1 := by
    rw [← transpose_mul, nonsing_inv_mul _ (Ne.isUnit hx₁), transpose_one]
  have e2 : x₂⁻¹.map conj * x₂.map conj = 1 := map_conj_inv (nonsing_inv_mul _ (Ne.isUnit hx₂))
  have a1 : (lin G P x₁ x₂)ᵀ * P = G * x₂.map conj * P := by
    rw [← hPt, ← transpose_mul, hPt, lin, (proj_parts hP _ _).1, transpose_mul, hPt,
      transpose_transpose]
  have a2 : P * anti G P x₁ x₂ = P * (x₁ᵀ * G) := (proj_parts hP _ _).1
  have l : anti G P x₁ x₂ * Gi * (lin G P x₁ x₂)ᵀ * P = P * x₁ᵀ * G * x₂.map conj * P := by
    rw [Matrix.mul_assoc, a1, Matrix.mul_assoc, ← Matrix.mul_assoc Gi, ← Matrix.mul_assoc Gi, hG',
      Matrix.one_mul, anti, Matrix.add_mul, Matrix.mul_assoc (1 - P), ← Matrix.mul_assoc (map _ _),
      e2, Matrix.one_mul, Matrix.sub_mul, hP, Matrix.one_mul, sub_self, add_zero]
    simp only [Matrix.mul_assoc]
  rw [l, ← Matrix.mul_assoc, ← Matrix.mul_assoc, a2, Matrix.mul_assoc P (x₁ᵀ * G),
    Matrix.mul_assoc x₁ᵀ G Gi, hG, Matrix.mul_one, lin, transpose_add, transpose_mul, transpose_mul (1 - P),
    transpose_sub, transpose_one, hPt, transpose_transpose, Matrix.mul_add, Matrix.mul_assoc P x₁ᵀ (x₁⁻¹ᵀ * _),
    ← Matrix.mul_assoc x₁ᵀ x₁⁻¹ᵀ, e1, Matrix.one_mul, Matrix.mul_sub, hP, Matrix.mul_one, sub_self, add_zero]
  simp only [Matrix.mul_assoc]

theorem cplx (hP : P * P = P) (hPt : Pᵀ = P) (hGh : Gᴴ = G) (hG : G * Gi = 1) (hc : c ≠ 0)
    (hc' : star c = -c) (hx₁ : x₁.det ≠ 0) (hx₂ : x₂.det ≠ 0) (h₁ : g₁ * u₁ = 1)
    (h₂ : g₂ * u₂ = 1) (hg₁ : g₁ᵀ * G * g₁.map conj = G) (hg₂ : g₂ᵀ * G * g₂.map conj = G)
    (hL : (lin G P x₁ x₂).det ≠ 0) (hA : (anti G P x₁ x₂).det ≠ 0)
    {S Z : Matrix (Fin r) (Fin r) ℂ}
    (hS : S = (lin G P x₁ x₂)⁻¹ * (1 - (2 : ℂ) • P) * lin G P x₁ x₂) (hZ : Z = c • (Sᵀ * G)) :
    ∃ M M' : Matrix (Fin r) (Fin r) ℂ, lin G P (g₁ * x₁) (g₂ * x₂) = lin G P x₁ x₂ * M ∧
      anti G P (g₁ * x₁) (g₂ * x₂) = anti G P x₁ x₂ * M' ∧
      ((2 * c)⁻¹ • (Gi * (u₁ᵀ - u₂ᵀ))) * Z + (2 : ℂ)⁻¹ • (Gi * (u₁ᵀ + u₂ᵀ) * G) = Gi * Mᵀ * G ∧
      Z * ((2 * c)⁻¹ • (Gi * (u₁ᵀ - u₂ᵀ)))ᴴ + ((2 : ℂ)⁻¹ • (Gi * (u₁ᵀ + u₂ᵀ) * G))ᴴ =
        G * M' * Gi ∧
      ((2 : ℂ)⁻¹ • (u₁ᵀ + u₂ᵀ)) * Z + (c / 2) • ((u₁ᵀ - u₂ᵀ) * G) = c • ((S * M)ᵀ * G) := by
  have hG' : Gi * G = 1 := mul_eq_one_comm.1 hG
  have hcm := comm_proj hP hPt hG hx₁ hx₂
  rw [lin_act hP h₁ h₂ hg₂, anti_act hP h₁ h₂ hg₁]
  generalize lin G P x₁ x₂ = L at *
  generalize anti G P x₁ x₂ = A at *
  have l1 : L * L⁻¹ = 1 := mul_nonsing_inv _ (Ne.isUnit hL)
  have l2 : L⁻¹ * L = 1 := nonsing_inv_mul _ (Ne.isUnit hL)
  have a1 : A * A⁻¹ = 1 := mul_nonsing_inv _ (Ne.isUnit hA)
  have a2 : A⁻¹ * A = 1 := nonsing_inv_mul _ (Ne.isUnit hA)
  have hGih : Giᴴ = Gi := by
    have : Giᴴ * G = 1 := by rw [← hGh, ← conjTranspose_mul, hG, conjTranspose_one]
    calc Giᴴ = Giᴴ * (G * Gi) := by rw [hG, Matrix.mul_one]
      _ = Gi := by rw [← Matrix.mul_assoc, this, Matrix.one_mul]
  set p := L⁻¹ * P * L with hp
  set p' := A⁻¹ * P * A with hp'
  have hS' : S = 1 - (2 : ℂ) • p := by
    rw [hS, hp, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, l2, Matrix.mul_smul,
      Matrix.smul_mul]
  have hpp : p * p = p := by
    calc p * p = L⁻¹ * P * (L * L⁻¹) * P * L := by simp only [hp, Matrix.mul_assoc]
      _ = p := by rw [l1, Matrix.mul_one, Matrix.mul_assoc L⁻¹, hP]
  have hLp : L * p = P * L := by rw [hp, ← Matrix.mul_assoc, ← Matrix.mul_assoc, l1, Matrix.one_mul]
  have hAp : A * p' = P * A := by
    rw [hp', ← Matrix.mul_assoc, ← Matrix.mul_assoc, a1, Matrix.one_mul]
  have hrel : pᵀ * G = G * p' := by
    have t : Lᵀ * L⁻¹ᵀ = 1 := by rw [← transpose_mul, l2, transpose_one]
    calc pᵀ * G = G * (A⁻¹ * A) * Gi * (Lᵀ * P * L⁻¹ᵀ * G) := by
          rw [a2, Matrix.mul_one, hG, Matrix.one_mul, hp, transpose_mul, transpose_mul, hPt]
          simp only [Matrix.mul_assoc]
      _ = G * A⁻¹ * (A * Gi * Lᵀ * P) * L⁻¹ᵀ * G := by simp only [Matrix.mul_assoc]
      _ = G * (A⁻¹ * P * A) * (Gi * (Lᵀ * L⁻¹ᵀ) * G) := by rw [hcm]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [t, Matrix.mul_one, hG', Matrix.mul_one]
  have hSt : Sᵀ = 1 - (2 : ℂ) • pᵀ := by rw [hS', transpose_sub, transpose_one, transpose_smul]
  refine ⟨p * u₂ + (1 - p) * u₁, p' * u₁.map conj + (1 - p') * u₂.map conj, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hLp,
      Matrix.mul_one, Matrix.one_mul]
  · simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hAp,
      Matrix.mul_one, Matrix.one_mul]
  · rw [hZ, hSt, den_eq _ _ _ hc]
    simp only [transpose_add, transpose_mul, transpose_sub, transpose_one]
  · have k : ∀ u : Matrix (Fin r) (Fin r) ℂ, uᵀᴴ = u.map conj := fun u => by ext; simp
    have e : (1 - (2 : ℂ) • pᵀ) * G = G * (1 - (2 : ℂ) • p') := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hrel, Matrix.one_mul,
        Matrix.mul_one]
    rw [hZ, hSt, e, ← den'_eq _ _ _ hc]
    simp only [conjTranspose_smul, conjTranspose_mul, conjTranspose_add, conjTranspose_sub, k, hGh,
      hGih, star_inv₀, star_mul', hc', star_ofNat]
  · have e : S * (p * u₂ + (1 - p) * u₁) = (1 - p) * u₁ - p * u₂ := by
      rw [hS']
      simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hpp,
        Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul]
      module
    rw [hZ, hSt, num_eq, e]
    simp only [transpose_mul, transpose_sub, transpose_one]

theorem gauss {C D Z Y' : Matrix (Fin r) (Fin r) ℂ} (h : C * Dᴴ = D * Cᴴ)
    (hQ : (C * Z + D).det ≠ 0) (hQ' : (Z * Cᴴ + Dᴴ).det ≠ 0) (hY : (imH Z).det ≠ 0)
    (hI : (C * Z + D)ᴴ * Y' * (C * Z + D) = imH Z) :
    (C * Z + D)⁻¹ * Y'⁻¹ * (Z * Cᴴ + Dᴴ)⁻¹ + (2 * I) • ((C * Z + D)⁻¹ * C) = (imH Z)⁻¹ := by
  have e1 : (C * Z + D)ᴴ = (Z * Cᴴ + Dᴴ) - (2 * I) • (imH Z * Cᴴ) := by
    have : (2 * I) * (2 * I)⁻¹ = 1 := mul_inv_cancel₀ (by simp)
    rw [imH, Matrix.smul_mul, smul_smul, this, one_smul, conjTranspose_add, conjTranspose_mul,
      Matrix.sub_mul]
    abel
  have e2 : (C * Z + D) * Cᴴ = C * (Z * Cᴴ + Dᴴ) := by
    rw [Matrix.add_mul, Matrix.mul_add, h, Matrix.mul_assoc]
  have hQh : (C * Z + D)ᴴ.det ≠ 0 := by rw [det_conjTranspose]; simpa using hQ
  generalize C * Z + D = Q at *
  generalize Z * Cᴴ + Dᴴ = Q' at *
  generalize imH Z = Y at *
  have e3 : Q⁻¹ * Y'⁻¹ = Y⁻¹ * Qᴴ := by
    rw [← hI, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_assoc,
      nonsing_inv_mul _ (Ne.isUnit hQh), Matrix.mul_one]
  have e4 : Cᴴ * Q'⁻¹ = Q⁻¹ * C := by
    calc _ = Q⁻¹ * (Q * Cᴴ) * Q'⁻¹ := by
          rw [← Matrix.mul_assoc Q⁻¹, nonsing_inv_mul _ (Ne.isUnit hQ), Matrix.one_mul]
      _ = _ := by
          rw [e2, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hQ'),
            Matrix.mul_one]
  rw [e3, e1, Matrix.mul_assoc, Matrix.sub_mul, mul_nonsing_inv _ (Ne.isUnit hQ'), Matrix.smul_mul,
    Matrix.mul_assoc, e4, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
    nonsing_inv_mul _ (Ne.isUnit hY), Matrix.one_mul, sub_add_cancel]

end Cplx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem kappa_ne : X.κ0 ≠ 0 := by
  have := X.ξ0_ne
  rcases X.κ0_xi with h | h <;> simp [h, this]

theorem cc_kappa : cc X.κ0 = -X.κ0 := by
  have := X.ξ0_im
  rw [cc] at this
  rcases X.κ0_xi with h | h <;> simp [h, cc, this, map_ofNat]

theorem ccT_Gm : ccT X.Gm = X.Gm := by
  ext a b
  exact X.Gm_herm b a

theorem un_mat {γ : GL (Fin r) E} (h : IsUn X γ) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * ccT (γ : Matrix (Fin r) (Fin r) E)ᵀ = X.Gm := by
  ext a b
  have := h (Pi.single a 1) (Pi.single b 1)
  simp only [herm, mulVec_single_one, Pi.single_apply, cc, apply_ite, map_one, map_zero] at this
  simp only [ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero] at this
  rw [← this, Finset.sum_comm]
  simp [Matrix.mul_apply, ccT, cc, Finset.sum_mul]

theorem dblT_left : Matrix.fromBlocks ((2 : E)⁻¹ • (1 : Matrix (Fin r) (Fin r) E)) (-((2 : E)⁻¹ • 1))
    ((2 * (X.κ0 / 4))⁻¹ • X.Gm⁻¹) ((2 * (X.κ0 / 4))⁻¹ • X.Gm⁻¹) * dblT X = 1 := by
  have hk := kappa_ne X
  have hG : X.Gm⁻¹ * X.Gm = 1 := nonsing_inv_mul _ (Ne.isUnit X.Gm_det)
  have e : (2 * (X.κ0 / 4))⁻¹ * (X.κ0 / 4) = 2⁻¹ := by field_simp
  rw [dblT, fromBlocks_multiply, ← fromBlocks_one]
  congr 1
  · simp only [Matrix.mul_one, Matrix.mul_neg, neg_neg]; module
  · simp
  · simp
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hG, e, mul_comm (X.κ0 / 4)]; module

theorem iota_eq (γ₁ γ₂ : GL (Fin r) E) : iota X γ₁ γ₂ = Matrix.fromBlocks
    ((2 : E)⁻¹ • ((γ₁⁻¹).1ᵀ + (γ₂⁻¹).1ᵀ)) ((X.κ0 / 4 / 2) • (((γ₁⁻¹).1ᵀ - (γ₂⁻¹).1ᵀ) * X.Gm))
    ((2 * (X.κ0 / 4))⁻¹ • (X.Gm⁻¹ * ((γ₁⁻¹).1ᵀ - (γ₂⁻¹).1ᵀ)))
    ((2 : E)⁻¹ • (X.Gm⁻¹ * ((γ₁⁻¹).1ᵀ + (γ₂⁻¹).1ᵀ) * X.Gm)) := by
  have hk := kappa_ne X
  have e : (2 * (X.κ0 / 4))⁻¹ * (X.κ0 / 4) = 2⁻¹ := by field_simp
  rw [iota, Matrix.inv_eq_left_inv (dblT_left X), dblT, fromBlocks_multiply, fromBlocks_multiply]
  generalize (γ₁⁻¹).1ᵀ = h₁
  generalize (γ₂⁻¹).1ᵀ = h₂
  congr 1 <;>
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
    Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_zero, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, smul_smul, e, mul_comm (X.κ0 / 4)] <;> module

theorem ccT_blocks (a b c d : Matrix (Fin r) (Fin r) E) :
    ccT (Matrix.fromBlocks a b c d) = Matrix.fromBlocks (ccT a) (ccT c) (ccT b) (ccT d) := by
  ext (i | i) (j | j) <;> rfl

theorem dblT_form : dblT X * Matrix.J (Fin r) E * ccT (dblT X) =
    Matrix.fromBlocks ((X.κ0 / 2) • X.Gm) 0 0 (-((X.κ0 / 2) • X.Gm)) := by
  have e1 : ccT ((X.κ0 / 4) • X.Gm) = -((X.κ0 / 4) • X.Gm) := by
    ext a b
    have h1 := cc_kappa X
    have h2 := X.Gm_herm b a
    rw [cc] at h1 h2
    simp [ccT, cc, h1, h2, map_ofNat, neg_div]
  have e2 : ccT (-1 : Matrix (Fin r) (Fin r) E) = -1 := by
    ext a b
    by_cases h : a = b <;> simp [ccT, cc, Matrix.one_apply, h, eq_comm]
  rw [dblT, ccT_blocks, e1, e2, HAct.ccT_one, Matrix.J, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;>
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, neg_neg] <;> module

theorem un_inv {γ : GL (Fin r) E} (h : IsUn X γ) :
    (γ⁻¹).1ᵀ * X.Gm * ccT (γ⁻¹).1ᵀ = X.Gm := by
  have e : (γ⁻¹).1ᵀ * γ.1ᵀ = 1 := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  calc _ = (γ⁻¹).1ᵀ * (γ.1ᵀ * X.Gm * ccT γ.1ᵀ) * ccT (γ⁻¹).1ᵀ := by rw [un_mat X h]
    _ = ((γ⁻¹).1ᵀ * γ.1ᵀ) * X.Gm * ccT ((γ⁻¹).1ᵀ * γ.1ᵀ) := by
        simp only [HAct.ccT_mul, Matrix.mul_assoc]
    _ = _ := by rw [e, HAct.ccT_one, Matrix.one_mul, Matrix.mul_one]

theorem iota_mem {γ₁ γ₂ : GL (Fin r) E} (h₁ : IsUn X γ₁) (h₂ : IsUn X γ₂) :
    iota X γ₁ γ₂ ∈ UU E r := by
  have hT : (dblT X)⁻¹ * dblT X = 1 := by
    rw [Matrix.inv_eq_left_inv (dblT_left X)]; exact dblT_left X
  have z : ccT (0 : Matrix (Fin r) (Fin r) E) = 0 := by ext; simp [ccT, cc]
  have hH : Matrix.fromBlocks (γ₁⁻¹).1ᵀ 0 0 (γ₂⁻¹).1ᵀ *
      (dblT X * Matrix.J (Fin r) E * ccT (dblT X)) *
      ccT (Matrix.fromBlocks (γ₁⁻¹).1ᵀ 0 0 (γ₂⁻¹).1ᵀ) =
      dblT X * Matrix.J (Fin r) E * ccT (dblT X) := by
    rw [dblT_form, ccT_blocks, z, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, un_inv X h₁, un_inv X h₂,
      smul_zero, neg_zero]
  have h : ccT (iota X γ₁ γ₂) ∈ UU E r := by
    change ccT (ccT _) * _ * _ = _
    rw [HAct.ccT_ccT, iota, HAct.ccT_mul, HAct.ccT_mul]
    calc _ = (dblT X)⁻¹ * (Matrix.fromBlocks (γ₁⁻¹).1ᵀ 0 0 (γ₂⁻¹).1ᵀ *
          (dblT X * Matrix.J (Fin r) E * ccT (dblT X)) *
          ccT (Matrix.fromBlocks (γ₁⁻¹).1ᵀ 0 0 (γ₂⁻¹).1ᵀ)) * ccT (dblT X)⁻¹ := by
            simp only [Matrix.mul_assoc]
      _ = ((dblT X)⁻¹ * dblT X) * Matrix.J (Fin r) E * ccT ((dblT X)⁻¹ * dblT X) := by
            rw [hH]; simp only [HAct.ccT_mul, Matrix.mul_assoc]
      _ = _ := by rw [hT, HAct.ccT_one, Matrix.one_mul, Matrix.mul_one]
  have := (HAct.group_part h).2.2.1
  rwa [HAct.ccT_ccT] at this

noncomputable def prj : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.diagonal fun a : Fin r => if (a : ℕ) < X.p0 then 1 else 0

theorem prj_sq : prj X * prj X = prj X := by
  rw [prj, diagonal_mul_diagonal]
  congr 1
  ext a
  split_ifs <;> simp

theorem aLin_eq (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) :
    aLin X x₁ x₂ τ = lin (X.Gm.map τ.1) (prj X) (mat x₁ τ) (mat x₂ τ) := by
  ext a c
  simp only [aLin, lin, prj, Matrix.sub_mul, Matrix.one_mul, Matrix.add_apply, Matrix.sub_apply,
    diagonal_mul, of_apply, transpose_apply]
  split_ifs <;> simp [Matrix.mul_apply, mat]

theorem aAnti_eq (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) :
    aAnti X x₁ x₂ τ = anti (X.Gm.map τ.1) (prj X) (mat x₁ τ) (mat x₂ τ) := by
  ext a c
  simp only [aAnti, anti, prj, Matrix.sub_mul, Matrix.one_mul, Matrix.add_apply, Matrix.sub_apply,
    diagonal_mul, of_apply, transpose_apply]
  split_ifs <;> simp [Matrix.mul_apply, mat]

theorem sgn_eq : Matrix.diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ)) =
    1 - (2 : ℂ) • prj X := by
  ext a b
  by_cases h : a = b
  · subst h
    simp only [prj, sgn, diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply, one_apply_eq]
    split_ifs <;> norm_num
  · simp [prj, h]

theorem place {γ₁ γ₂ : GL (Fin r) E} (h₁ : IsUn X γ₁) (h₂ : IsUn X γ₂) {x₁ x₂ : Frame X.Ψ r}
    (hx₁ : x₁ ∈ X.dom) (hx₂ : x₂ ∈ X.dom) (τ : X.Ψ) (hL : (aLin X x₁ x₂ τ).det ≠ 0)
    (hA : (aAnti X x₁ x₂ τ).det ≠ 0) :
    ∃ M M' : Matrix (Fin r) (Fin r) ℂ, aLin X (lact γ₁ x₁) (lact γ₂ x₂) τ = aLin X x₁ x₂ τ * M ∧
      aAnti X (lact γ₁ x₁) (lact γ₂ x₂) τ = aAnti X x₁ x₂ τ * M' ∧
      X.Gm.map τ.1 * hDen X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) τ = Mᵀ * X.Gm.map τ.1 ∧
      hDen' X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) τ * X.Gm.map τ.1 = X.Gm.map τ.1 * M' ∧
      (iota X γ₁ γ₂).toBlocks₁₁.map τ.1 * dblZ X x₁ x₂ τ + (iota X γ₁ γ₂).toBlocks₁₂.map τ.1 =
        (τ.1 X.κ0 / 4) • (((aLin X x₁ x₂ τ)⁻¹ *
          Matrix.diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ)) * aLin X x₁ x₂ τ * M)ᵀ *
          X.Gm.map τ.1) := by
  have hG : X.Gm.map τ.1 * X.Gm⁻¹.map τ.1 = 1 := by
    rw [← Matrix.map_mul, mul_nonsing_inv _ (Ne.isUnit X.Gm_det)]; simp
  have hG' := mul_eq_one_comm.1 hG
  have hu : ∀ γ : GL (Fin r) E, γ.1.map τ.1 * (γ⁻¹).1.map τ.1 = 1 := fun γ => by
    rw [← Matrix.map_mul, Units.mul_inv]; simp
  have hg : ∀ γ, IsUn X γ →
      (γ.1.map τ.1)ᵀ * X.Gm.map τ.1 * (γ.1.map τ.1).map conj = X.Gm.map τ.1 := fun γ h => by
    have := congrArg (fun m => m.map τ.1) (un_mat X h)
    simp only [Matrix.map_mul, HAct.map_ccT] at this
    exact this
  have hc : τ.1 X.κ0 / 4 ≠ 0 := by simp [kappa_ne X]
  have hc' : star (τ.1 X.κ0 / 4) = -(τ.1 X.κ0 / 4) := by
    rw [Complex.star_def, map_div₀, ← HAct.emb_cc, cc_kappa, map_neg, map_ofNat, neg_div]
  have hGh : (X.Gm.map τ.1)ᴴ = X.Gm.map τ.1 := by rw [← HAct.map_ccT, ccT_Gm]
  rw [aLin_eq] at hL
  rw [aAnti_eq] at hA
  obtain ⟨M, M', m1, m2, m3, m4, m5⟩ := cplx (prj_sq X) (diagonal_transpose _) hGh hG hc hc'
    (hx₁ τ).1 (hx₂ τ).1 (hu γ₁) (hu γ₂) (hg γ₁ h₁) (hg γ₂ h₂) hL hA rfl rfl
  have sm : ∀ (s : E) (m : Matrix (Fin r) (Fin r) E), (s • m).map τ.1 = τ.1 s • m.map τ.1 :=
    fun s m => by ext; simp
  have ad : ∀ (s m : Matrix (Fin r) (Fin r) E), (s + m).map τ.1 = s.map τ.1 + m.map τ.1 :=
    fun s m => by ext; simp
  have sb : ∀ (s m : Matrix (Fin r) (Fin r) E), (s - m).map τ.1 = s.map τ.1 - m.map τ.1 :=
    fun s m => by ext; simp
  simp only [hDen, hDen', dblZ, iota_eq, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂,
    toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, sm, ad, sb, Matrix.map_mul, transpose_map,
    map_inv₀, map_mul, map_div₀, map_ofNat, sgn_eq, aLin_eq, aAnti_eq]
  refine ⟨M, M', m1, m2, ?_, ?_, m5⟩
  · rw [m3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hG, Matrix.one_mul]
  · rw [m4, Matrix.mul_assoc, hG', Matrix.mul_one]

theorem inv_swap {a q m : Matrix (Fin r) (Fin r) ℂ} (h : a * q = m * a) (hq : q.det ≠ 0)
    (hm : m.det ≠ 0) : a * q⁻¹ = m⁻¹ * a := by
  calc a * q⁻¹ = m⁻¹ * (m * a) * q⁻¹ := by
        rw [← Matrix.mul_assoc m⁻¹, nonsing_inv_mul _ (Ne.isUnit hm), Matrix.one_mul]
    _ = _ := by
        rw [← h, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hq),
          Matrix.mul_one]

theorem det_swap {a q m : Matrix (Fin r) (Fin r) ℂ} (h : a * q = m * a) (ha : a.det ≠ 0) :
    q.det = m.det := by
  have := congrArg det h
  rw [det_mul, det_mul, mul_comm m.det] at this
  exact mul_left_cancel₀ ha this

theorem of_at {α β : Type} (f : α → β → ℂ) (k : α) : Matrix.of f k = f k := rfl

theorem det_factor {l a q d : ℂ} (hl : l ≠ 0) (ha : a ≠ 0) (hq : q ≠ 0) (hd : d ≠ 0) (m : ℕ) :
    ((l * (q * d) * (a * q)) ^ m)⁻¹ * (q * d) ^ (m + m) = d ^ m * ((l * a) ^ m)⁻¹ := by
  simp only [mul_pow, pow_add]
  field_simp

theorem exp_factor {a b c d u v w : ℂ} (h : a * b = d * c) (h' : u + v = w) :
    a * cexp u * (b * cexp v) = d * (c * cexp w) := by
  rw [mul_mul_mul_comm, h, ← Complex.exp_add, h', mul_assoc]

end GlobalTheory.SW.DblPair

open GlobalTheory.SW.DblPair in

theorem GlobalTheory.SW.iota_act_dbl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ₁ γ₂ : GL (Fin r) E, IsUn X γ₁ → IsUn X γ₂ → iota X γ₁ γ₂ ∈ UU E r ∧ ∃ a : ℂ, a ≠ 0 ∧ ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, hAct X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) = dblZ X (lact γ₁ x₁) (lact γ₂ x₂) ∧ ∀ z₁ w : Fin n → Fin g → ℂ, (dblz X idx (lact γ₁ x₁) (lact γ₂ x₂) z₁ w = fun τ => Matrix.of fun k => (hDen' X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) τ)⁻¹ *ᵥ dblz X idx x₁ x₂ z₁ w τ k) ∧ (dblz' X idx (lact γ₁ x₁) (lact γ₂ x₂) z₁ w = fun τ => Matrix.of fun k => dblz' X idx x₁ x₂ z₁ w τ k ᵥ* (hDen X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) τ)⁻¹) ∧ kZero X idx (lact γ₁ x₁) (lact γ₂ x₂) z₁ w * hFac X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w) = a * kZero X idx x₁ x₂ z₁ w := by
  intro E _ _ _ r X g bas idx n _ hn γ₁ γ₂ h₁ h₂
  have hι := iota_mem X h₁ h₂
  obtain ⟨⟨g1, -, g3, -⟩, hact⟩ := unitary_act_halfSpace E X.Ψ r _ hι
  refine ⟨hι, ∏ τ : X.Ψ, τ.1 (iota X γ₁ γ₂).det ^ (n / 2), ?_, fun x₁ hx₁ x₂ hx₂ => ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ((map_ne_zero _).2 g1.ne_zero)
  obtain ⟨-, hZ, hd⟩ := GlobalTheory.SW.dblZ_mem_Hn E r X x₁ hx₁ x₂ hx₂
  have hq := (hact _ hZ).1
  choose M M' m1 m2 m3 m4 m5 using fun τ => place X h₁ h₂ hx₁ hx₂ τ (hd τ).1 (hd τ).2.1
  have hG : ∀ τ : X.Ψ, (X.Gm.map τ.1).det ≠ 0 := fun τ => by
    have : (X.Gm.map τ.1).det = τ.1 X.Gm.det := (RingHom.map_det τ.1 X.Gm).symm
    rw [this]
    exact (map_ne_zero _).2 X.Gm_det
  have hQ' : ∀ τ, (hDen' X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) τ).det ≠ 0 := fun τ h =>
    (hq τ).1 (by rw [← (hq τ).2.1, h, zero_mul])
  have dM : ∀ τ, (M τ).det = (hDen X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) τ).det := fun τ => by
    rw [det_swap (m3 τ) (hG τ), det_transpose]
  have dM' : ∀ τ, (M' τ).det = (hDen' X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) τ).det := fun τ =>
    det_swap (m4 τ).symm (hG τ)
  have i1 : ∀ τ, X.Gm.map τ.1 * (hDen X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) τ)⁻¹ =
      (M τ)⁻¹ᵀ * X.Gm.map τ.1 := fun τ => by
    rw [inv_swap (m3 τ) (hq τ).1 (by rw [det_transpose, dM]; exact (hq τ).1),
      transpose_nonsing_inv]
  have i2 : ∀ τ, X.Gm.map τ.1 * (M' τ)⁻¹ =
      (hDen' X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) τ)⁻¹ * X.Gm.map τ.1 := fun τ =>
    inv_swap (m4 τ).symm (by rw [dM']; exact hQ' τ) (hQ' τ)
  have hA : hAct X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) = dblZ X (lact γ₁ x₁) (lact γ₂ x₂) := by
    funext τ
    rw [hAct, m5, Matrix.smul_mul, Matrix.mul_assoc, i1]
    simp only [dblZ, m1, Matrix.mul_inv_rev, transpose_mul, Matrix.mul_assoc]
  refine ⟨hA, fun z₁ w => ?_⟩
  have hz : dblz X idx (lact γ₁ x₁) (lact γ₂ x₂) z₁ w = fun τ => Matrix.of fun k =>
      (hDen' X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) τ)⁻¹ *ᵥ dblz X idx x₁ x₂ z₁ w τ k := by
    funext τ k
    simp only [dblz, of_at, m2, Matrix.mul_inv_rev, mulVec_smul, mulVec_mulVec,
      ← Matrix.mul_assoc, i2]
  have hz' : dblz' X idx (lact γ₁ x₁) (lact γ₂ x₂) z₁ w = fun τ => Matrix.of fun k =>
      dblz' X idx x₁ x₂ z₁ w τ k ᵥ* (hDen X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) τ)⁻¹ := by
    funext τ k
    simp only [dblz', of_at, m1, Matrix.mul_inv_rev, smul_vecMul, vecMul_vecMul, i1]
    rw [← mulVec_mulVec, ← vecMul_vecMul, vecMul_transpose]
  refine ⟨hz, hz', ?_⟩
  have hb := fun τ : X.Ψ => HAct.map_mem τ.1 g3
  rw [kZero, kZero, hFac, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, hz, hz', ← hA]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hcd : (iota X γ₁ γ₂).toBlocks₂₁.map τ.1 * ((iota X γ₁ γ₂).toBlocks₂₂.map τ.1)ᴴ =
      (iota X γ₁ γ₂).toBlocks₂₂.map τ.1 * ((iota X γ₁ γ₂).toBlocks₂₁.map τ.1)ᴴ := by
    have h := hb τ
    rw [HAct.map_ccT, HAct.map_blocks, fromBlocks_conjTranspose] at h
    simpa only [conjTranspose_conjTranspose] using (HAct.blocks h).2.2.2
  have hga : (hDen X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) τ)⁻¹ *
      (imH (hAct X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) τ))⁻¹ *
      (hDen' X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) τ)⁻¹ +
      (2 * I) • ((hDen X.Ψ (iota X γ₁ γ₂) (dblZ X x₁ x₂) τ)⁻¹ *
        (iota X γ₁ γ₂).toBlocks₂₁.map τ.1) = (imH (dblZ X x₁ x₂ τ))⁻¹ :=
    gauss hcd (hq τ).1 (hQ' τ) (hZ τ).det_pos.ne' (hq τ).2.2.2
  obtain ⟨m, rfl⟩ := hn
  have hm : (m + m) / 2 = m := by omega
  refine exp_factor ?_ ?_
  · rw [m1, m2, det_mul, det_mul, dM, dM', hm, ← (hq τ).2.1]
    exact det_factor (hd τ).1 (hd τ).2.1 (hQ' τ) ((map_ne_zero _).2 g1.ne_zero) m
  · rw [← hga]
    simp only [of_at, add_mulVec, dotProduct_add, Finset.sum_add_distrib, smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← Finset.mul_sum, ← dotProduct_mulVec, mulVec_mulVec,
      Matrix.mul_assoc]
    ring
