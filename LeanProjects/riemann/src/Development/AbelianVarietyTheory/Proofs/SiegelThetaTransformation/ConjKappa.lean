import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHnStatement
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblPer

theorem transport {m : Type} [Fintype m] [DecidableEq m] (A B G D : Matrix m m ℂ)
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) (hG : G.det ≠ 0) (hD : Dᵀ = D)
    (h : D * (B * G⁻¹ * Aᵀ) = B * G⁻¹ * Aᵀ * D) :
    G * B⁻¹ * D * B = (A⁻¹ * D * A)ᵀ * G := by
  have hAt : IsUnit Aᵀ.det := by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hA
  have hB' : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hG' : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hD, Matrix.transpose_nonsing_inv]

  set N := Aᵀ⁻¹ * G * B⁻¹ with hN
  have hMN : B * G⁻¹ * Aᵀ * N = 1 := by
    rw [hN]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hAt, Matrix.nonsing_inv_mul_cancel_left _ _ hG',
      Matrix.mul_nonsing_inv _ hB']
  have hNM : N * (B * G⁻¹ * Aᵀ) = 1 := by
    rw [hN]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hB', Matrix.mul_nonsing_inv_cancel_left _ _ hG',
      Matrix.nonsing_inv_mul _ hAt]
  have hND : N * D = D * N := by
    calc N * D = N * D * (B * G⁻¹ * Aᵀ * N) := by rw [hMN, Matrix.mul_one]
      _ = N * (D * (B * G⁻¹ * Aᵀ)) * N := by simp only [Matrix.mul_assoc]
      _ = N * (B * G⁻¹ * Aᵀ * D) * N := by rw [h]
      _ = (N * (B * G⁻¹ * Aᵀ)) * D * N := by simp only [Matrix.mul_assoc]
      _ = D * N := by rw [hNM, Matrix.one_mul]
  have hAN : Aᵀ * N = G * B⁻¹ := by
    rw [hN]; simp only [Matrix.mul_assoc]; rw [Matrix.mul_nonsing_inv_cancel_left _ _ hAt]
  calc G * B⁻¹ * D * B = Aᵀ * N * D * B := by rw [hAN]
    _ = Aᵀ * (N * D) * B := by simp only [Matrix.mul_assoc]
    _ = Aᵀ * (D * N) * B := by rw [hND]
    _ = Aᵀ * D * Aᵀ⁻¹ * G * (B⁻¹ * B) := by rw [hN]; simp only [Matrix.mul_assoc]
    _ = Aᵀ * (D * Aᵀ⁻¹) * G := by
      rw [Matrix.nonsing_inv_mul _ hB', Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem of_row {m n : Type} (f : m → n → ℂ) (k : m) : Matrix.of f k = f k := rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) := by
  simp only [cc]
  rw [IsCMField.complexEmbedding_complexConj]

theorem cc_kappa : cc X.κ0 = -X.κ0 := by
  have h := X.ξ0_im
  simp only [cc] at h ⊢
  rcases X.κ0_xi with h' | h' <;> rw [h'] <;> simp [map_mul, map_neg, h]

theorem kappa_ne : X.κ0 ≠ 0 := by
  rcases X.κ0_xi with h | h <;> rw [h] <;> simp [X.ξ0_ne]

theorem conj_kappa (τ : E →+* ℂ) : conj (τ X.κ0) = -τ X.κ0 := by rw [← emb_cc, cc_kappa X, map_neg]

theorem conj_Gm (τ : E →+* ℂ) (a b : Fin r) : conj (τ (X.Gm a b)) = τ (X.Gm b a) := by rw [← emb_cc, X.Gm_herm]

theorem det_Gm (τ : E →+* ℂ) : (X.Gm.map τ).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero τ).mpr X.Gm_det

noncomputable abbrev dg : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ))

private theorem ent_ofSL_eq_coe {m : Type} [Fintype m] (A B C : Matrix m m ℂ) (a d : m) :
    (A * B * Cᵀ) a d = A a ⬝ᵥ (B *ᵥ C d) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem comm (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) (h₁ : (mat x₁ τ).det ≠ 0) (h₂ : (mat x₂ τ).det ≠ 0) :
    dg X * (aAnti X x₁ x₂ τ * (X.Gm.map τ.1)⁻¹ * (aLin X x₁ x₂ τ)ᵀ) =
      aAnti X x₁ x₂ τ * (X.Gm.map τ.1)⁻¹ * (aLin X x₁ x₂ τ)ᵀ * dg X := by
  have hGu : IsUnit (X.Gm.map τ.1).det := isUnit_iff_ne_zero.mpr (det_Gm X τ.1)
  have hu₁ : IsUnit (mat x₁ τ).det := isUnit_iff_ne_zero.mpr h₁
  have hu₂ : IsUnit (mat x₂ τ).det := isUnit_iff_ne_zero.mpr h₂
  ext a d
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases ha : (a : ℕ) < X.p0 <;> by_cases hd : (d : ℕ) < X.p0
  · rw [show sgn X.p0 a = sgn X.p0 d by simp [sgn, ha, hd]]; ring
  ·
    have hP : (aAnti X x₁ x₂ τ * (X.Gm.map τ.1)⁻¹ * (aLin X x₁ x₂ τ)ᵀ) a d = 0 := by
      rw [ent_ofSL_eq_coe]
      have e1 : aAnti X x₁ x₂ τ a = (fun b => x₁ τ b a) ᵥ* X.Gm.map τ.1 := by
        ext c; simp [aAnti, ha, Matrix.vecMul, dotProduct]
      have e2 : aLin X x₁ x₂ τ d = (mat x₁ τ)⁻¹ d := by
        ext c; simp [aLin, hd]
      rw [e1, e2, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGu,
        Matrix.one_mulVec]
      have h0 : ((mat x₁ τ)⁻¹ * mat x₁ τ) d a = 0 := by
        rw [Matrix.nonsing_inv_mul _ hu₁, Matrix.one_apply_ne]
        intro hda; rw [hda] at hd; exact hd ha
      rw [Matrix.mul_apply] at h0
      rw [← h0, dotProduct]
      exact Finset.sum_congr rfl fun b _ => by simp [mat, mul_comm]
    rw [hP]; simp
  ·
    have hP : (aAnti X x₁ x₂ τ * (X.Gm.map τ.1)⁻¹ * (aLin X x₁ x₂ τ)ᵀ) a d = 0 := by
      rw [ent_ofSL_eq_coe]
      have e1 : aAnti X x₁ x₂ τ a = fun c => conj ((mat x₂ τ)⁻¹ a c) := by
        ext c; simp [aAnti, ha]
      have e2 : aLin X x₁ x₂ τ d = X.Gm.map τ.1 *ᵥ fun b => conj (x₂ τ b d) := by
        ext c; simp [aLin, hd, Matrix.mulVec, dotProduct]
      rw [e1, e2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hGu, Matrix.one_mulVec]
      have h0 : ((mat x₂ τ)⁻¹ * mat x₂ τ) a d = 0 := by
        rw [Matrix.nonsing_inv_mul _ hu₂, Matrix.one_apply_ne]
        intro had; rw [had] at ha; exact ha hd
      rw [Matrix.mul_apply] at h0
      have h0' := congrArg (starRingEnd ℂ) h0
      rw [map_sum, map_zero] at h0'
      rw [← h0', dotProduct]
      exact Finset.sum_congr rfl fun c _ => by simp [mat]
    rw [hP]; simp
  · rw [show sgn X.p0 a = sgn X.p0 d by simp [sgn, ha, hd]]; ring

theorem lin_coord (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) (v₁ v₂ : Fin r → E) :
    (fun a : Fin r => if (a : ℕ) < X.p0 then conj (per X x₂ v₂ (τ, a)) else per X x₁ v₁ (τ, a)) =
      (2⁻¹ : ℂ) • (aLin X x₁ x₂ τ *ᵥ (Data.emb τ.1 v₁ + Data.emb τ.1 v₂) +
        (dg X * aLin X x₁ x₂ τ) *ᵥ (Data.emb τ.1 v₁ - Data.emb τ.1 v₂)) := by
  ext a
  simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_diagonal, smul_eq_mul]
  by_cases ha : (a : ℕ) < X.p0
  · have hL : ∀ w : Fin r → ℂ,
        (aLin X x₁ x₂ τ *ᵥ w) a = ∑ c, (∑ b, τ.1 (X.Gm c b) * conj (x₂ τ b a)) * w c := by
      intro w; simp [Matrix.mulVec, dotProduct, aLin, ha]
    have hc : conj (per X x₂ v₂ (τ, a)) = (aLin X x₁ x₂ τ *ᵥ Data.emb τ.1 v₂) a := by
      rw [hL, per_of_lt X x₂ v₂ τ ha]
      simp only [hermC, FD.col, mat, Matrix.of_apply, map_sum, map_mul, Complex.conj_conj,
        conj_Gm, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring
    rw [if_pos ha, hc]
    simp only [sgn, if_pos ha]
    push_cast
    ring
  · have hL : ∀ w : Fin r → ℂ, (aLin X x₁ x₂ τ *ᵥ w) a = ((mat x₁ τ)⁻¹ *ᵥ w) a := by
      intro w; simp [Matrix.mulVec, dotProduct, aLin, ha]
    rw [if_neg ha, per_of_le X x₁ v₁ τ (not_lt.mp ha), hL, hL]
    simp only [sgn, if_neg ha]
    push_cast
    ring

theorem anti_coord (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) (v₁ v₂ : Fin r → E) :
    (fun a : Fin r => if (a : ℕ) < X.p0 then per X x₁ v₁ (τ, a) else conj (per X x₂ v₂ (τ, a))) =
      (2⁻¹ : ℂ) • (aAnti X x₁ x₂ τ *ᵥ (star (Data.emb τ.1 v₁) + star (Data.emb τ.1 v₂)) -
        (dg X * aAnti X x₁ x₂ τ) *ᵥ (star (Data.emb τ.1 v₁) - star (Data.emb τ.1 v₂))) := by
  ext a
  simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_diagonal, smul_eq_mul]
  by_cases ha : (a : ℕ) < X.p0
  · have hc : per X x₁ v₁ (τ, a) = (aAnti X x₁ x₂ τ *ᵥ star (Data.emb τ.1 v₁)) a := by
      rw [per_of_lt X x₁ v₁ τ ha]
      simp only [Matrix.mulVec, dotProduct, aAnti, Matrix.of_apply, if_pos ha, hermC, FD.col, mat,
        Finset.sum_mul, Pi.star_apply, Complex.star_def]
      exact Finset.sum_comm
    rw [if_pos ha, hc]
    simp only [sgn, if_pos ha]
    push_cast
    ring
  · have hc : conj (per X x₂ v₂ (τ, a)) = (aAnti X x₁ x₂ τ *ᵥ star (Data.emb τ.1 v₂)) a := by
      rw [per_of_le X x₂ v₂ τ (not_lt.mp ha)]
      simp only [Matrix.mulVec, dotProduct, aAnti, Matrix.of_apply, if_neg ha, map_sum, map_mul,
        Pi.star_apply, Complex.star_def]
    rw [if_neg ha, hc]
    simp only [sgn, if_neg ha]
    push_cast
    ring

theorem cols {n : ℕ} (y₁ y₂ : Matrix (Fin n) (Fin r) E) :
    Matrix.fromCols y₁ y₂ * dblT X =
      Matrix.fromCols (y₁ - y₂) ((X.κ0 / 4) • ((y₁ + y₂) * X.Gm)) := by
  rw [dblT, Matrix.fromCols_mul_fromBlocks]
  congr 1
  · simp [sub_eq_add_neg]
  · rw [Matrix.mul_smul, Matrix.mul_smul, ← smul_add, Matrix.add_mul]

theorem ccT_dblT : ccT (dblT X) =
    Matrix.fromBlocks 1 (-1) (-((X.κ0 / 4) • X.Gm)) (-((X.κ0 / 4) • X.Gm)) := by
  have hm : ∀ s t : E, cc (s * t) = cc s * cc t := fun s t => map_mul (IsCMField.complexConj E) s t
  have hd : ∀ s t : E, cc (s / t) = cc s / cc t := fun s t => map_div₀ (IsCMField.complexConj E) s t
  have h4 : cc (4 : E) = 4 := map_ofNat (IsCMField.complexConj E) 4
  have h0 : cc (0 : E) = 0 := map_zero (IsCMField.complexConj E)
  have h1 : cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
  have hn : ∀ s : E, cc (-s) = -cc s := fun s => map_neg (IsCMField.complexConj E) s
  unfold ccT dblT
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]
  congr 1
  · ext a b
    by_cases hab : a = b
    · subst hab; simp [h1]
    · simp [hab, Ne.symm hab, h0]
  · ext a b
    by_cases hab : a = b
    · subst hab; simp [hn, h1]
    · simp [hab, Ne.symm hab, h0]
  · ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.neg_apply,
      smul_eq_mul]
    rw [hm, hd, h4, cc_kappa X, X.Gm_herm]
    ring
  · ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.neg_apply,
      smul_eq_mul]
    rw [hm, hd, h4, cc_kappa X, X.Gm_herm]
    ring

theorem dbl_per : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ y₁ y₂ : Matrix (Fin n) (Fin r) E, (∀ τ, dblz' X idx x₁ x₂ (fun k => per X x₁ (y₁ k) ∘ idx) (fun k i => conj (per X x₂ (y₂ k) (idx i))) τ = ((Matrix.fromCols y₁ y₂ * dblT X).toCols₂).map τ.1 + ((Matrix.fromCols y₁ y₂ * dblT X).toCols₁).map τ.1 * dblZ X x₁ x₂ τ) ∧ (∀ τ, dblz X idx x₁ x₂ (fun k => per X x₁ (y₁ k) ∘ idx) (fun k i => conj (per X x₂ (y₂ k) (idx i))) τ = (((Matrix.fromCols y₁ y₂ * dblT X).toCols₂).map τ.1).map conj + (((Matrix.fromCols y₁ y₂ * dblT X).toCols₁).map τ.1).map conj * (dblZ X x₁ x₂ τ)ᵀ) ∧ IsUnit (dblT X).det ∧ dblT X * Matrix.J (Fin r) E * ccT (dblT X) = (X.κ0 / 2) • Matrix.fromBlocks X.Gm 0 0 (-X.Gm) := by
  intro E _ _ _ r X g bas idx n _ _ x₁ hx₁ x₂ hx₂ y₁ y₂
  have hI := GlobalTheory.T.dblZ_mem_Hn_and_det_ne_zero E r X x₁ hx₁ x₂ hx₂
  have hm₁ : ∀ τ, (mat x₁ τ).det ≠ 0 := fun τ => (hx₁ τ).1
  have hm₂ : ∀ τ, (mat x₂ τ).det ≠ 0 := fun τ => (hx₂ τ).1

  have hD4 : dblT X * Matrix.J (Fin r) E * ccT (dblT X) =
      (X.κ0 / 2) • Matrix.fromBlocks X.Gm 0 0 (-X.Gm) := by
    rw [ccT_dblT, dblT, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_smul]
    congr 1 <;> ext i j <;> simp <;> ring
  have hC : IsUnit (dblT X).det := by
    have h := congrArg Matrix.det hD4
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Matrix.det_fromBlocks_zero₂₁] at h
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0] at h
    simp [kappa_ne X, X.Gm_det, Matrix.det_neg] at h
  refine ⟨fun τ => ?_, fun τ => ?_, hC, hD4⟩
  · have hL : IsUnit (aLin X x₁ x₂ τ).det := isUnit_iff_ne_zero.mpr (hI.2.2 τ).1
    rw [cols X y₁ y₂, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols]
    ext k j
    simp only [dblz', Matrix.of_apply, Function.comp_apply, Equiv.apply_symm_apply]
    rw [lin_coord X x₁ x₂ τ (y₁ k) (y₂ k), Matrix.mulVec_smul, Matrix.mulVec_add,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hL, Matrix.one_mulVec,
      Matrix.add_apply, Matrix.mul_apply_eq_vecMul]
    have h1 : ((y₁ - y₂).map τ.1) k = Data.emb τ.1 (y₁ k) - Data.emb τ.1 (y₂ k) := by
      ext i; simp [Data.emb]
    have h2 : (((X.κ0 / 4) • ((y₁ + y₂) * X.Gm)).map τ.1) k j =
        τ.1 X.κ0 / 4 * ((Data.emb τ.1 (y₁ k) + Data.emb τ.1 (y₂ k)) ᵥ* X.Gm.map τ.1) j := by
      have h4 : τ.1 (4 : E) = 4 := map_ofNat τ.1 4
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Data.emb, map_sum, Finset.mul_sum,
        add_mul, h4]
    rw [h1, h2, dblZ]
    simp only [Matrix.vecMul_smul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose,
      Matrix.smul_vecMul, Matrix.add_vecMul, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
      Matrix.mul_assoc]
    ring
  · have hL : (aLin X x₁ x₂ τ).det ≠ 0 := (hI.2.2 τ).1
    have hA : IsUnit (aAnti X x₁ x₂ τ).det := isUnit_iff_ne_zero.mpr (hI.2.2 τ).2.1
    have htr := transport (aLin X x₁ x₂ τ) (aAnti X x₁ x₂ τ) (X.Gm.map τ.1) (dg X) hL
      (hI.2.2 τ).2.1 (det_Gm X τ.1) (Matrix.diagonal_transpose _)
      (comm X x₁ x₂ τ (hm₁ τ) (hm₂ τ))
    rw [cols X y₁ y₂, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols]
    ext k j
    simp only [dblz, Matrix.of_apply, Function.comp_apply, Equiv.apply_symm_apply]
    rw [anti_coord X x₁ x₂ τ (y₁ k) (y₂ k), Matrix.mulVec_smul, Matrix.mulVec_sub,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec,
      Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.add_apply, Matrix.mul_apply_eq_vecMul]
    have h1 : (((y₁ - y₂).map τ.1).map (starRingEnd ℂ)) k =
        star (Data.emb τ.1 (y₁ k)) - star (Data.emb τ.1 (y₂ k)) := by
      ext i; simp [Data.emb]
    have h2 : ((((X.κ0 / 4) • ((y₁ + y₂) * X.Gm)).map τ.1).map (starRingEnd ℂ)) k j =
        -(τ.1 X.κ0 / 4) *
          (X.Gm.map τ.1 *ᵥ (star (Data.emb τ.1 (y₁ k)) + star (Data.emb τ.1 (y₂ k)))) j := by
      have hk := conj_kappa X τ.1
      have hG := conj_Gm X τ.1
      have h4 : τ.1 (4 : E) = 4 := map_ofNat τ.1 4
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.add_apply,
        smul_eq_mul, map_mul, map_div₀, map_sum, map_add, h4, hk, hG, Matrix.mulVec, dotProduct,
        Pi.add_apply, Pi.star_apply, Data.emb, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Complex.star_def, map_ofNat]
      ring
    have htr' : ((aLin X x₁ x₂ τ)⁻¹ * Matrix.diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ)) *
        aLin X x₁ x₂ τ)ᵀ * X.Gm.map τ.1 =
        X.Gm.map τ.1 * (aAnti X x₁ x₂ τ)⁻¹ * dg X * aAnti X x₁ x₂ τ := htr.symm
    rw [h1, h2, dblZ, Matrix.vecMul_transpose, htr']
    simp only [Matrix.smul_mulVec, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Matrix.mul_assoc]
    ring

end GlobalTheory.SW.DblPer
