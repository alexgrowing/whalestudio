import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivEqSumList

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.KernSym

noncomputable section

section Matrices

variable {r : ℕ}

local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

def cj (M : Mat) : Mat := M.map conj

theorem cj_mul (M N : Mat) : cj (M * N) = cj M * cj N := Matrix.map_mul

theorem cj_cj (M : Mat) : cj (cj M) = M := by ext; simp [cj]

theorem cj_transpose (M : Mat) : cj Mᵀ = (cj M)ᵀ := rfl

theorem conjTranspose_eq (M : Mat) : Mᴴ = (cj M)ᵀ := rfl

theorem cj_inv (M : Mat) : cj M⁻¹ = (cj M)⁻¹ := by
  have h := congrArg transpose (conjTranspose_nonsing_inv M)
  rwa [transpose_nonsing_inv] at h

theorem det_cj (M : Mat) : (cj M).det = conj M.det := ((starRingEnd ℂ).map_det M).symm

theorem cj_smul (c : ℂ) (M : Mat) : cj (c • M) = conj c • cj M := by ext; simp [cj]

def mix (p : ℕ) (M N : Mat) : Mat := Matrix.of fun a c => if (a : ℕ) < p then M a c else N a c

theorem mix_mul (p : ℕ) (M N U : Mat) : mix p M N * U = mix p (M * U) (N * U) := by
  ext a c
  simp only [mix, mul_apply, of_apply]
  split_ifs <;> rfl

def ptZ (κ : ℂ) (G S A : Mat) : Mat := (κ / 4) • ((A⁻¹ * S * A)ᵀ * G)

def expM (κ : ℂ) (G S A B : Mat) : Mat :=
  (-(κ / 2) * (κ / 2)) • (A⁻¹ᵀ * G * (imH (ptZ κ G S A))⁻¹ * G * B⁻¹)

theorem imH_conj (Z V : Mat) : imH (Vᴴ * Z * V) = Vᴴ * imH Z * V := by
  simp only [imH, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

theorem imH_neg_conjTranspose (Z : Mat) : imH (-Zᴴ) = imH Z := by
  simp only [imH, conjTranspose_neg, conjTranspose_conjTranspose]
  congr 1
  abel

theorem imH_conjTranspose (Z : Mat) : (imH Z)ᴴ = imH Z := by
  unfold imH
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose,
    ← neg_sub Z, smul_neg, ← neg_smul]
  congr 1
  simp

theorem det_mul_det_cj {G U : Mat} (hG : G.det ≠ 0) (hU : Uᵀ * G * cj U = G) :
    U.det * (cj U).det = 1 := by
  have h := congrArg det hU
  rw [det_mul, det_mul, det_transpose] at h
  apply mul_left_cancel₀ hG
  linear_combination h

theorem expM_unitary (κ : ℂ) {G U : Mat} (S A B : Mat) (hG : G.det ≠ 0) (hU : Uᵀ * G * cj U = G) :
    expM κ G S (A * U⁻¹) (B * (cj U)⁻¹) = expM κ G S A B := by
  have hd := det_mul_det_cj hG hU
  have h1 : IsUnit U.det := IsUnit.of_mul_eq_one _ hd
  have h2 : IsUnit (cj U).det := IsUnit.of_mul_eq_one_right _ hd
  have h3 : Uᵀ * G = G * (cj U)⁻¹ := by
    conv_rhs => rw [← hU, mul_nonsing_inv_cancel_right _ _ h2]
  have h4 : ((cj U)⁻¹)ᴴ = U⁻¹ᵀ := by rw [conjTranspose_eq, cj_inv, cj_cj]
  have h5 : ptZ κ G S (A * U⁻¹) = ((cj U)⁻¹)ᴴ * ptZ κ G S A * (cj U)⁻¹ := by
    simp only [ptZ, h4, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ h1, transpose_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h3]
  have h6 (M : Mat) : Uᵀ * (G * (cj U * M)) = G * M := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU]
  rw [expM, h5, imH_conj]
  simp only [expM, h4, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ h1,
    nonsing_inv_nonsing_inv _ h2, transpose_mul, ← transpose_nonsing_inv, Matrix.mul_assoc, h6]

theorem expM_swap {κ : ℂ} {G S A B : Mat} (hκ : conj κ = -κ) (hG : Gᴴ = G) (hS : cj S = S)
    (hS' : Sᵀ = S) (hd : G.det ≠ 0) (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (h : A * Gᵀ⁻¹ * Bᵀ * S = S * (A * Gᵀ⁻¹ * Bᵀ)) :
    expM κ G S (cj B) (cj A) = (expM κ G S A B)ᴴ := by
  have uA : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have uB : IsUnit Bᵀ.det := isUnit_iff_ne_zero.2 (by rwa [det_transpose])
  have uG : IsUnit Gᵀ.det := isUnit_iff_ne_zero.2 (by rwa [det_transpose])
  have hG' : cj Gᵀ = G := hG
  have h1 : Bᵀ * S * Bᵀ⁻¹ * Gᵀ = Gᵀ * (A⁻¹ * S * A) := by
    have := congrArg (fun M => Gᵀ * A⁻¹ * M * Bᵀ⁻¹ * Gᵀ) h
    simpa only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ uA,
      mul_nonsing_inv_cancel_left _ _ uG, mul_nonsing_inv_cancel_left _ _ uB,
      nonsing_inv_mul _ uG, Matrix.mul_one] using this
  have h2 := congrArg cj h1
  simp only [cj_mul, cj_inv, hG', hS] at h2
  have h3 : ptZ κ G S (cj B) = -(ptZ κ G S A)ᴴ := by
    simp only [ptZ, conjTranspose_smul, conjTranspose_mul, hG]
    rw [conjTranspose_eq, cj_transpose, transpose_transpose, cj_mul, cj_mul, cj_inv, hS, ← h2,
      ← neg_smul, transpose_mul, transpose_mul, hS', transpose_nonsing_inv, cj_transpose,
      ← Matrix.mul_assoc]
    congr 1
    simp [hκ, neg_div]
  simp only [expM, h3, imH_neg_conjTranspose, conjTranspose_smul, conjTranspose_mul, hG,
    conjTranspose_nonsing_inv, imH_conjTranspose, Matrix.mul_assoc, transpose_nonsing_inv]
  congr 1
  simp [hκ, neg_div]

theorem expM_ortho {t : ℝ} (ht : t ≠ 0) {G S x : Mat} (hS : S * S = 1) (hSt : Sᵀ = S)
    (hx : xᵀ * G * cj x = S) :
    expM (-(I * t)) G (-S) x⁻¹ (cj x)⁻¹ = (t : ℂ) • (1 : Mat) := by
  have hd := congrArg det hx
  have hd' := congrArg det hS
  rw [det_mul, det_mul, det_transpose] at hd
  rw [det_mul, det_one] at hd'
  have h0 : x.det * G.det * (cj x).det ≠ 0 := by rw [hd]; exact left_ne_zero_of_mul_eq_one hd'
  have h1 : IsUnit x.det := isUnit_iff_ne_zero.2 (left_ne_zero_of_mul (left_ne_zero_of_mul h0))
  have h1' : IsUnit xᵀ.det := by rwa [det_transpose]
  have h2 : IsUnit (cj x).det := isUnit_iff_ne_zero.2 (right_ne_zero_of_mul h0)
  have h3 : xᵀ * G = S * (cj x)⁻¹ := by rw [← hx, mul_nonsing_inv_cancel_right _ _ h2]
  have h3' : G * cj x = xᵀ⁻¹ * S := by
    rw [← hx, Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ h1']
  have hS1 (M : Mat) : S * (S * M) = M := by rw [← Matrix.mul_assoc, hS, Matrix.one_mul]
  have h4 : ((cj x)⁻¹)ᴴ = xᵀ⁻¹ := by rw [conjTranspose_eq, cj_inv, cj_cj, transpose_nonsing_inv]
  have h5 : ptZ (-(I * t)) G (-S) x⁻¹ = ((cj x)⁻¹)ᴴ * ((I * t / 4 : ℂ) • (1 : Mat)) * (cj x)⁻¹ := by
    simp only [ptZ, h4, nonsing_inv_nonsing_inv _ h1, transpose_mul, transpose_neg,
      transpose_nonsing_inv, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, h3, hSt, hS1,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, neg_div, neg_smul, smul_neg, neg_neg]
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht
  have h6 : (imH ((I * t / 4 : ℂ) • (1 : Mat)))⁻¹ = (4 / t : ℂ) • (1 : Mat) := by
    apply inv_eq_left_inv
    rw [imH, conjTranspose_smul, conjTranspose_one, ← sub_smul, smul_smul, Matrix.smul_mul,
      Matrix.one_mul, smul_smul]
    convert one_smul ℂ (1 : Mat)
    simp only [star_div₀, star_mul', star_ofNat, Complex.star_def, conj_I, conj_ofReal]
    field_simp
    ring
  have h7 (M : Mat) : xᵀ * (G * (cj x * M)) = S * M := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hx]
  have h8 : xᵀ * (G * cj x) = S := by rw [← Matrix.mul_assoc, hx]
  rw [expM, h5, imH_conj]
  simp only [Matrix.mul_inv_rev, h4, h6, nonsing_inv_nonsing_inv _ h1, nonsing_inv_nonsing_inv _ h1',
    nonsing_inv_nonsing_inv _ h2, Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.one_mul, h7, h8, hS, smul_smul]
  congr 1
  field_simp
  linear_combination (-4 : ℂ) * I_sq

end Matrices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} (X : Data E r)
  (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r)

theorem aLin_eq (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) :
    aLin X x₁ x₂ τ = mix X.p0 ((cj (mat x₂ τ))ᵀ * (X.Gm.map τ.1)ᵀ) (mat x₁ τ)⁻¹ := by
  ext a c
  simp only [aLin, mix, of_apply, mul_apply, transpose_apply, map_apply, cj, mat, mul_comm]

theorem aAnti_eq (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) :
    aAnti X x₁ x₂ τ = mix X.p0 ((mat x₁ τ)ᵀ * X.Gm.map τ.1) (cj (mat x₂ τ))⁻¹ := by
  rw [← cj_inv]
  ext a c
  simp only [aAnti, mix, of_apply, mul_apply, transpose_apply, map_apply, cj, mat]

theorem map_Gm_conjTranspose (τ : X.Ψ) : (X.Gm.map τ.1)ᴴ = X.Gm.map τ.1 := by
  ext a b
  simp only [conjTranspose_apply, map_apply, Complex.star_def, ← emb_cc, X.Gm_herm]

theorem det_map_Gm (τ : X.Ψ) : (X.Gm.map τ.1).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero τ.1).2 X.Gm_det

theorem gram_eq_mul (τ : X.Ψ) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ.1 X.Gm M = Mᵀ * X.Gm.map τ.1 * cj M := by
  ext a b
  simp only [FD.gram, hermC, FD.col, of_apply, mul_apply, transpose_apply, map_apply, cj,
    Finset.sum_mul]
  rw [Finset.sum_comm]

def mixV (τ : X.Ψ) (z w : Fin g → ℂ) : Fin r → ℂ := fun a =>
  if (a : ℕ) < X.p0 then z (idx.symm (τ, a)) else w (idx.symm (τ, a))

def kM (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  expM (τ.1 X.κ0) (X.Gm.map τ.1) (-sgnM X) (aLin X x₁ x₂ τ) (aAnti X x₁ x₂ τ)

theorem kZero_eq (x₁ x₂ : Frame X.Ψ r) (z w : Fin n → Fin g → ℂ) :
    kZero X idx x₁ x₂ z w =
      ∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹ *
        cexp (Real.pi * ∑ k, mixV X idx τ (w k) (z k) ⬝ᵥ kM X x₁ x₂ τ *ᵥ mixV X idx τ (z k) (w k)) := by
  refine Finset.prod_congr rfl fun τ _ => ?_
  congr 3
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : dblZ X x₁ x₂ τ = ptZ (τ.1 X.κ0) (X.Gm.map τ.1) (-sgnM X) (aLin X x₁ x₂ τ) := by
    rw [ptZ, sgnM, diagonal_neg]
    rfl
  rw [h, kM, expM]
  change ((τ.1 X.κ0 / 2) • ((_ *ᵥ mixV X idx τ (w k) (z k)) ᵥ* _)) ⬝ᵥ _ *ᵥ
    ((-(τ.1 X.κ0 / 2)) • (_ *ᵥ _ *ᵥ mixV X idx τ (z k) (w k))) = _
  rw [smul_dotProduct, mulVec_smul, dotProduct_smul, smul_mulVec, dotProduct_smul, smul_smul,
    mul_comm, ← vecMul_transpose, ← dotProduct_mulVec, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

theorem analyticAt_kZero (x₁ x₂ : Frame X.Ψ r) (p : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ)) :
    AnalyticAt ℂ (fun p : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) =>
      kZero X idx x₁ x₂ p.1 p.2) p := by
  simp only [kZero_eq, dotProduct, mulVec]
  refine Finset.analyticAt_fun_prod _ fun τ _ =>
    SCV.analyticAt_iff_eventually_differentiableAt.2 (.of_forall fun p => ?_)
  have h (τ : X.Ψ) (k : Fin n) : DifferentiableAt ℂ
      (fun p : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) => mixV X idx τ (p.1 k) (p.2 k)) p ∧
      DifferentiableAt ℂ
      (fun p : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) => mixV X idx τ (p.2 k) (p.1 k)) p := by
    constructor <;> refine differentiableAt_pi.2 fun a => ?_ <;> unfold mixV <;> split_ifs <;>
      fun_prop
  exact .const_mul (.cexp (.const_mul (.fun_sum fun k _ =>
    .fun_sum fun a _ => .fun_mul (differentiableAt_pi.1 (h τ k).2 a) (.fun_sum fun b _ =>
      .const_mul (differentiableAt_pi.1 (h τ k).1 b) _)) _)) _

theorem kZero_lmulC {u : X.Ψ → Matrix (Fin r) (Fin r) ℂ}
    (hu : ∀ (τ : X.Ψ) v w, hermC τ.1 X.Gm (u τ *ᵥ v) (u τ *ᵥ w) = hermC τ.1 X.Gm v w)
    (x₁ x₂ : Frame X.Ψ r) :
    kZero (n := n) X idx (X.lmulC u x₁) (X.lmulC u x₂) = kZero X idx x₁ x₂ := by
  funext z w
  rw [kZero_eq, kZero_eq]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hU : (u τ)ᵀ * X.Gm.map τ.1 * cj (u τ) = X.Gm.map τ.1 := by
    rw [← gram_eq_mul]
    ext a b
    have := hu τ (Pi.single a 1) (Pi.single b 1)
    simp only [mulVec_single_one] at this
    refine this.trans ?_
    simp [hermC, Pi.single_apply, apply_ite]
  have hd := det_mul_det_cj (det_map_Gm X τ) hU
  have h1 : IsUnit (u τ).det := IsUnit.of_mul_eq_one _ hd
  have h2 : IsUnit (cj (u τ)).det := IsUnit.of_mul_eq_one_right _ hd
  have hm (x : Frame X.Ψ r) : mat (X.lmulC u x) τ = u τ * mat x τ := rfl
  have h3 : (u τ)ᵀ * X.Gm.map τ.1 = X.Gm.map τ.1 * (cj (u τ))⁻¹ := by
    conv_rhs => rw [← hU, mul_nonsing_inv_cancel_right _ _ h2]
  have h4 : (cj (u τ))ᵀ * (X.Gm.map τ.1)ᵀ = (X.Gm.map τ.1)ᵀ * (u τ)⁻¹ := by
    conv_rhs => rw [← hU, transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc,
      mul_nonsing_inv_cancel_right _ _ h1]
  have hA : aLin X (X.lmulC u x₁) (X.lmulC u x₂) τ = aLin X x₁ x₂ τ * (u τ)⁻¹ := by
    simp only [aLin_eq, mix_mul, hm, cj_mul, transpose_mul, Matrix.mul_inv_rev, Matrix.mul_assoc, h4]
  have hB : aAnti X (X.lmulC u x₁) (X.lmulC u x₂) τ = aAnti X x₁ x₂ τ * (cj (u τ))⁻¹ := by
    simp only [aAnti_eq, mix_mul, hm, cj_mul, transpose_mul, Matrix.mul_inv_rev, Matrix.mul_assoc,
      h3]
  rw [kM, kM, hA, hB, expM_unitary _ _ _ _ (det_map_Gm X τ) hU, det_mul, det_mul, det_nonsing_inv,
    det_nonsing_inv, Ring.inverse_eq_inv', mul_mul_mul_comm, ← mul_inv, hd, inv_one, mul_one]

theorem sgnM_mul_self : sgnM X * sgnM X = 1 := by
  rw [sgnM, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  unfold sgn
  split_ifs <;> simp

theorem cj_sgnM : cj (-sgnM X) = -sgnM X := by
  ext a b
  by_cases h : a = b <;> simp [cj, sgnM, diagonal_apply, h]

variable {X} in

theorem aLin_aAnti_comm {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) (τ : X.Ψ) :
    aLin X x₁ x₂ τ * (X.Gm.map τ.1)ᵀ⁻¹ * (aAnti X x₁ x₂ τ)ᵀ * -sgnM X =
      -sgnM X * (aLin X x₁ x₂ τ * (X.Gm.map τ.1)ᵀ⁻¹ * (aAnti X x₁ x₂ τ)ᵀ) := by
  have uG : IsUnit (X.Gm.map τ.1).det := isUnit_iff_ne_zero.2 (det_map_Gm X τ)
  have uG' : IsUnit (X.Gm.map τ.1)ᵀ.det := by rwa [det_transpose]
  have u₁ : IsUnit (mat x₁ τ)ᵀ.det := isUnit_iff_ne_zero.2 (by rw [det_transpose]; exact (h₁ τ).1)
  have u₂ : IsUnit (cj (mat x₂ τ)).det :=
    isUnit_iff_ne_zero.2 (by rw [det_cj]; exact (map_ne_zero _).2 (h₂ τ).1)
  have e (N : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
      (N * (aAnti X x₁ x₂ τ)ᵀ) a b = (aAnti X x₁ x₂ τ * Nᵀ) b a := by
    rw [← transpose_apply (aAnti X x₁ x₂ τ * Nᵀ), transpose_mul, transpose_transpose]
  ext a b
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_apply, neg_apply, sgnM, mul_diagonal, diagonal_mul,
    aLin_eq, mix_mul, mix_mul, mul_nonsing_inv_cancel_right _ _ uG', mix, of_apply, e, e,
    aAnti_eq, mix_mul, mix_mul, transpose_transpose, nonsing_inv_mul _ u₂, transpose_mul,
    transpose_nonsing_inv, transpose_nonsing_inv, transpose_transpose, Matrix.mul_assoc _ (X.Gm.map τ.1) (_ * _),
    mul_nonsing_inv_cancel_left _ _ uG, mul_nonsing_inv _ u₁]
  simp only [mix, of_apply, sgn]
  split_ifs with ha hb hb
  · exact congrArg _ (mul_comm _ _)
  · rw [one_apply_ne (by rintro rfl; exact hb ha)]; simp
  · rw [one_apply_ne (by rintro rfl; exact ha hb)]; simp
  · exact congrArg _ (mul_comm _ _)

theorem conj_kappa (τ : X.Ψ) : conj (τ.1 X.κ0) = -τ.1 X.κ0 :=
  Complex.ext (by simp [DblPoint.re_kappa]) (by simp)

variable {X} in

theorem kZero_swap {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom)
    (z w : Fin n → Fin g → ℂ) :
    kZero X idx x₂ x₁ z w = conj (kZero X idx x₁ x₂ (star w) (star z)) := by
  rw [kZero_eq, kZero_eq, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hA : aLin X x₂ x₁ τ = cj (aAnti X x₁ x₂ τ) := DblPoint.aLin_swap X x₁ x₂ τ
  have hB : aAnti X x₂ x₁ τ = cj (aLin X x₁ x₂ τ) := by
    rw [← cj_cj (aAnti X x₂ x₁ τ)]
    exact congrArg cj (DblPoint.aLin_swap X x₂ x₁ τ).symm
  have hM : kM X x₂ x₁ τ = (kM X x₁ x₂ τ)ᴴ := by
    rw [kM, hA, hB]
    exact expM_swap (conj_kappa X τ) (map_Gm_conjTranspose X τ) (cj_sgnM X)
      (by rw [transpose_neg, sgnM, diagonal_transpose]) (det_map_Gm X τ)
      (DblPoint.det_aLin_ne_zero h₁ h₂ τ) (DblPoint.det_aAnti_ne_zero h₁ h₂ τ)
      (aLin_aAnti_comm h₁ h₂ τ)
  have hv (a b : Fin g → ℂ) : mixV X idx τ (star a) (star b) = star (mixV X idx τ a b) := by
    funext c
    simp only [mixV, Pi.star_apply, apply_ite star]
  rw [hM, hA, hB, det_cj, det_cj, map_mul, map_inv₀, map_pow, map_mul, ← Complex.exp_conj, map_mul,
    conj_ofReal, map_sum, mul_comm (conj _) (conj _)]
  congr 3
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.star_apply, hv]
  simp only [dotProduct, mulVec, conjTranspose_apply, Pi.star_apply, Complex.star_def, map_sum,
    map_mul, Complex.conj_conj, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

variable {X} in

theorem kZero_ortho {x : Frame X.Ψ r} (hx : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = sgnM X)
    (z w : Fin n → Fin g → ℂ) :
    kZero X idx x x z w = ((∏ τ : X.Ψ, normSq (mat x τ).det ^ (n / 2) : ℝ) : ℂ) *
      cexp (∑ τ : X.Ψ, ∑ a, ∑ k, ((π * -(τ.1 X.κ0).im : ℝ) : ℂ) * z k (idx.symm (τ, a)) *
        w k (idx.symm (τ, a))) := by
  rw [kZero_eq, Complex.exp_sum, ofReal_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h := hx τ
  rw [gram_eq_mul] at h
  have hd := congrArg det h
  have hd' := congrArg det (sgnM_mul_self X)
  rw [det_mul, det_mul, det_transpose] at hd
  rw [det_mul, det_one] at hd'
  have h0 := left_ne_zero_of_mul_eq_one hd'
  rw [← hd] at h0
  have h1 : IsUnit (mat x τ).det :=
    isUnit_iff_ne_zero.2 (left_ne_zero_of_mul (left_ne_zero_of_mul h0))
  have h2 : IsUnit (cj (mat x τ)).det := isUnit_iff_ne_zero.2 (right_ne_zero_of_mul h0)
  have hSt : (sgnM X)ᵀ = sgnM X := by rw [sgnM, diagonal_transpose]
  have hmix (M : Matrix (Fin r) (Fin r) ℂ) : mix X.p0 (sgnM X * M) M = M := by
    ext a c
    simp only [mix, of_apply, sgnM, diagonal_mul, sgn]
    split_ifs <;> simp
  have hA : aLin X x x τ = (mat x τ)⁻¹ := by
    refine (aLin_eq X x x τ).trans ((congrArg (mix X.p0 · _) ?_).trans (hmix _))
    rw [← hSt, ← h, transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc,
      mul_nonsing_inv_cancel_right _ _ h1]
  have hB : aAnti X x x τ = (cj (mat x τ))⁻¹ := by
    refine (aAnti_eq X x x τ).trans ((congrArg (mix X.p0 · _) ?_).trans (hmix _))
    rw [← h, mul_nonsing_inv_cancel_right _ _ h2]
  have hκ : τ.1 X.κ0 = -(I * (-(τ.1 X.κ0).im : ℝ)) :=
    Complex.ext (by simp [DblPoint.re_kappa]) (by simp)
  have hM : kM X x x τ = ((-(τ.1 X.κ0).im : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
    rw [kM, hA, hB, ← expM_ortho (neg_pos.2 (X.κ0_sign τ)).ne' (sgnM_mul_self X) hSt h, ← hκ]
  rw [hM, hA, hB, det_nonsing_inv, det_nonsing_inv, Ring.inverse_eq_inv', ← mul_inv, inv_pow,
    inv_inv, det_cj, mul_conj, ofReal_pow, Finset.sum_comm, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mulVec, one_mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [mixV, Pi.smul_apply, smul_eq_mul, ofReal_mul]
  split_ifs <;> ring

def letterCoord (l : Harm.Var X.Ψ q0 X.p0 (Fin n)) : (Fin n → Fin g → ℂ) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ)
    (idx.symm (rowOf X hr (l.1, l.2.1)))).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin g → ℂ) l.2.2)

theorem letterCoord_letterDir (l l' : Harm.Var X.Ψ q0 X.p0 (Fin n)) :
    letterCoord X hr idx l (letterDir X hr idx l') = if l = l' then 1 else 0 := by
  obtain ⟨τ, a, k⟩ := l
  obtain ⟨τ', a', k'⟩ := l'
  by_cases hk : k = k' <;> simp [letterCoord, letterDir, Pi.single_apply, hk, -rowOf_apply]

variable {X} in

theorem kern_pos {m : ℕ} (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (hP : ∃ j, P j ≠ 0)
    {x : Frame X.Ψ r} (hx : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = sgnM X) :
    0 < (kern X hr idx P x x).re := by
  set t : Harm.Var X.Ψ q0 X.p0 (Fin n) → ℝ := fun l => π * -(l.1.1 X.κ0).im with ht
  have tpos (l) : 0 < t l := mul_pos Real.pi_pos (neg_pos.2 (X.κ0_sign l.1))
  have hC : 0 < ∏ τ : X.Ψ, normSq (mat x τ).det ^ (n / 2) := by
    refine Finset.prod_pos fun τ _ => pow_pos (normSq_pos.2 fun h0 => ?_) _
    have hd := congrArg det (hx τ)
    have hd' := congrArg det (sgnM_mul_self X)
    rw [gram_eq_mul, det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul] at hd
    rw [det_mul, det_one, ← hd, zero_mul] at hd'
    exact zero_ne_one hd'
  have h (z : Fin n → Fin g → ℂ) : kZero X idx x x z = fun w =>
      ((∏ τ : X.Ψ, normSq (mat x τ).det ^ (n / 2) : ℝ) : ℂ) *
        cexp (∑ l, t l * letterCoord X hr idx l z * letterCoord X hr idx l w) := by
    funext w
    rw [kZero_ortho idx hx, Fintype.sum_prod_type]
    congr 2
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_prod_type, ← (rowIdx hr).sum_comp]
    rfl
  simp only [kern, biDeriv, h, polyDeriv_barP_exp _ _ _ (letterCoord_letterDir X hr idx), re_sum,
    ofReal_re]
  obtain ⟨j, hj⟩ := hP
  refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ _, mul_pos hC (apolar_norm_pos hj tpos)⟩
  by_cases hi : P i = 0
  · simp [hi]
  · exact (mul_pos hC (apolar_norm_pos hi tpos)).le

variable {X} in

theorem kern_swap {m : ℕ} (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) {x₁ x₂ : Frame X.Ψ r}
    (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) :
    kern X hr idx P x₂ x₁ = conj (kern X hr idx P x₁ x₂) := by
  rw [kern, kern, biDeriv, biDeriv, map_sum]
  refine Finset.sum_congr rfl fun j _ => polyDeriv_barP_symm _ _ (fun l => ?_)
    (analyticAt_kZero X idx x₁ x₂) (analyticAt_kZero X idx x₂ x₁) (kZero_swap idx h₁ h₂)
  simp [letterDir]

end

end GlobalTheory.SW.KernSym

namespace GlobalTheory.SW

theorem kern_invariant_symm_pos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), Even n → (∀ j, P j ∈ Harm.rowHighest ℂ c c') → (∀ u : X.Ψ → Matrix (Fin r) (Fin r) ℂ, (∀ (τ : X.Ψ) v w, hermC τ.1 X.Gm (u τ *ᵥ v) (u τ *ᵥ w) = hermC τ.1 X.Gm v w) → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, kern X hr idx P (X.lmulC u x₁) (X.lmulC u x₂) = kern X hr idx P x₁ x₂) ∧ (∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, kern X hr idx P x₂ x₁ = conj (kern X hr idx P x₁ x₂)) ∧ ((∃ j, P j ≠ 0) → ∀ x₀ : Frame X.Ψ r, (∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) = sgnM X) → 0 < (kern X hr idx P x₀ x₀).re) :=
  fun _ _ _ _ _ X _ _ hr idx _ _ _ _ P _ _ =>
    ⟨fun _ hu x₁ _ x₂ _ => by rw [kern, kern, KernSym.kZero_lmulC X idx hu],
      fun _ h₁ _ h₂ => KernSym.kern_swap hr idx P h₁ h₂,
      fun hP _ hx => KernSym.kern_pos hr idx P hP hx⟩

end GlobalTheory.SW
