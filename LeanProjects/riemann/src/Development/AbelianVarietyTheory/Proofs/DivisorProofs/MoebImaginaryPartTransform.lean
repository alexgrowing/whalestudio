import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff

namespace GlobalTheory.SiegelMoeb

theorem sp_block_rel {g : ℕ} (γ : Sp g) :
    γ.mat.toBlocks₂₁ᵀ * γ.mat.toBlocks₁₁ = γ.mat.toBlocks₁₁ᵀ * γ.mat.toBlocks₂₁ ∧
    γ.mat.toBlocks₂₂ᵀ * γ.mat.toBlocks₁₂ = γ.mat.toBlocks₁₂ᵀ * γ.mat.toBlocks₂₂ ∧
    γ.mat.toBlocks₂₂ᵀ * γ.mat.toBlocks₁₁ - γ.mat.toBlocks₁₂ᵀ * γ.mat.toBlocks₂₁ = 1 ∧
    γ.mat.toBlocks₁₁ᵀ * γ.mat.toBlocks₂₂ - γ.mat.toBlocks₂₁ᵀ * γ.mat.toBlocks₁₂ = 1 := by
  have h := SymplecticGroup.mem_iff'.mp γ.2
  have hm : (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) = γ.mat := rfl
  rw [hm, ← fromBlocks_toBlocks γ.mat] at h
  rw [fromBlocks_transpose, J, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [Matrix.mul_zero, Matrix.mul_neg, Matrix.mul_one, zero_add, add_zero, Matrix.neg_mul,
    Matrix.zero_mul] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← sub_eq_zero]; rw [← h1]; abel
  · rw [← sub_eq_zero]; rw [← h4]; abel
  · rw [← h3]; abel
  · rw [← neg_neg (1 : Matrix (Fin g) (Fin g) ℝ), ← h2]; abel

private abbrev cx {g : ℕ} (M : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g) (Fin g) ℂ :=
  M.map (fun t : ℝ => (t : ℂ))

private theorem cx_eq {g : ℕ} (M : Matrix (Fin g) (Fin g) ℝ) :
    cx M = (Complex.ofRealHom : ℝ →+* ℂ).mapMatrix M := rfl

private theorem cx_mul {g : ℕ} (M N : Matrix (Fin g) (Fin g) ℝ) : cx (M * N) = cx M * cx N := by
  simp only [cx_eq, map_mul]

private theorem cx_sub {g : ℕ} (M N : Matrix (Fin g) (Fin g) ℝ) : cx (M - N) = cx M - cx N := by
  simp only [cx_eq, map_sub]

private theorem cx_one {g : ℕ} : cx (1 : Matrix (Fin g) (Fin g) ℝ) = 1 := by
  simp only [cx_eq, map_one]

private theorem cx_transpose {g : ℕ} (M : Matrix (Fin g) (Fin g) ℝ) : cx Mᵀ = (cx M)ᵀ := by
  ext i j; rfl

private theorem cx_conjTranspose {g : ℕ} (M : Matrix (Fin g) (Fin g) ℝ) : (cx M)ᴴ = (cx M)ᵀ := by
  ext i j; simp [conjTranspose_apply]

private theorem key {g : ℕ} (γ : Sp g) (X Y : Matrix (Fin g) (Fin g) ℂ) :
    (Y * (cx γ.mat.toBlocks₂₁)ᵀ + (cx γ.mat.toBlocks₂₂)ᵀ) *
        (cx γ.mat.toBlocks₁₁ * X + cx γ.mat.toBlocks₁₂) -
      (Y * (cx γ.mat.toBlocks₁₁)ᵀ + (cx γ.mat.toBlocks₁₂)ᵀ) *
        (cx γ.mat.toBlocks₂₁ * X + cx γ.mat.toBlocks₂₂) = X - Y := by
  obtain ⟨h1, h2, h3, h4⟩ := sp_block_rel γ
  set a := γ.mat.toBlocks₁₁
  set b := γ.mat.toBlocks₁₂
  set c := γ.mat.toBlocks₂₁
  set d := γ.mat.toBlocks₂₂
  have e1 : (cx c)ᵀ * cx a - (cx a)ᵀ * cx c = 0 := by
    rw [← cx_transpose, ← cx_transpose, ← cx_mul, ← cx_mul, h1, sub_self]
  have e2 : (cx d)ᵀ * cx b - (cx b)ᵀ * cx d = 0 := by
    rw [← cx_transpose, ← cx_transpose, ← cx_mul, ← cx_mul, h2, sub_self]
  have e3 : (cx d)ᵀ * cx a - (cx b)ᵀ * cx c = 1 := by
    rw [← cx_transpose, ← cx_transpose, ← cx_mul, ← cx_mul, ← cx_sub, h3, cx_one]
  have e4 : (cx a)ᵀ * cx d - (cx c)ᵀ * cx b = 1 := by
    rw [← cx_transpose, ← cx_transpose, ← cx_mul, ← cx_mul, ← cx_sub, h4, cx_one]
  have hid : (Y * (cx c)ᵀ + (cx d)ᵀ) * (cx a * X + cx b) - (Y * (cx a)ᵀ + (cx b)ᵀ) * (cx c * X + cx d)
      = Y * ((cx c)ᵀ * cx a - (cx a)ᵀ * cx c) * X - Y * ((cx a)ᵀ * cx d - (cx c)ᵀ * cx b)
        + ((cx d)ᵀ * cx a - (cx b)ᵀ * cx c) * X + ((cx d)ᵀ * cx b - (cx b)ᵀ * cx d) := by
    noncomm_ring
  rw [hid, e1, e2, e3, e4]
  noncomm_ring

theorem im_moeb : ∀ {g : ℕ} (γ : Sp g) (T : Matrix (Fin g) (Fin g) ℂ), T.IsSymm →
    IsUnit (den γ T) → (moeb γ T).map (fun t => (t.im : ℂ)) =
      ((den γ T)⁻¹)ᴴ * T.map (fun t => (t.im : ℂ)) * (den γ T)⁻¹ := by
  intro g γ T hT hD
  have hdet : IsUnit (den γ T).det := (Matrix.isUnit_iff_isUnit_det _).mp hD
  set D := den γ T with hDdef
  set A := cx γ.mat.toBlocks₁₁ * T + cx γ.mat.toBlocks₁₂ with hAdef
  have hm : moeb γ T = A * D⁻¹ := rfl
  have hDd : D = cx γ.mat.toBlocks₂₁ * T + cx γ.mat.toBlocks₂₂ := rfl
  have hTt : Tᵀ = T := hT

  have hDt : Dᵀ = Tᵀ * (cx γ.mat.toBlocks₂₁)ᵀ + (cx γ.mat.toBlocks₂₂)ᵀ := by
    rw [hDd, transpose_add, transpose_mul]
  have hAt : Aᵀ = Tᵀ * (cx γ.mat.toBlocks₁₁)ᵀ + (cx γ.mat.toBlocks₁₂)ᵀ := by
    rw [hAdef, transpose_add, transpose_mul]
  have hDh : Dᴴ = Tᴴ * (cx γ.mat.toBlocks₂₁)ᵀ + (cx γ.mat.toBlocks₂₂)ᵀ := by
    rw [hDd, conjTranspose_add, conjTranspose_mul, cx_conjTranspose, cx_conjTranspose]
  have hAh : Aᴴ = Tᴴ * (cx γ.mat.toBlocks₁₁)ᵀ + (cx γ.mat.toBlocks₁₂)ᵀ := by
    rw [hAdef, conjTranspose_add, conjTranspose_mul, cx_conjTranspose, cx_conjTranspose]
  have kT : Dᵀ * A - Aᵀ * D = 0 := by
    rw [hDt, hAt, hDd, hAdef, key γ T Tᵀ, hTt, sub_self]
  have kH : Dᴴ * A - Aᴴ * D = T - Tᴴ := by
    rw [hDh, hAh, hDd, hAdef, key γ T Tᴴ]
  have hDi : D * D⁻¹ = 1 := mul_nonsing_inv D hdet

  have hsym : (A * D⁻¹)ᵀ = A * D⁻¹ := by
    have h1 : (D⁻¹)ᵀ * Dᵀ = 1 := by rw [← transpose_mul, hDi, transpose_one]
    have h2 : Dᵀ * A = Aᵀ * D := sub_eq_zero.mp kT
    calc (A * D⁻¹)ᵀ = (D⁻¹)ᵀ * Aᵀ * (D * D⁻¹) := by rw [hDi, Matrix.mul_one, transpose_mul]
      _ = (D⁻¹)ᵀ * (Aᵀ * D) * D⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (D⁻¹)ᵀ * Dᵀ * A * D⁻¹ := by rw [← h2]; simp only [Matrix.mul_assoc]
      _ = A * D⁻¹ := by rw [h1, Matrix.one_mul]

  have hIm : ∀ M : Matrix (Fin g) (Fin g) ℂ,
      M - M.map star = (2 * Complex.I) • M.map (fun t => (t.im : ℂ)) := by
    intro M; ext i j
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    apply Complex.ext <;> simp <;> ring
  have hmapT : T.map star = Tᴴ := by
    rw [conjTranspose, hTt]
  have hmapM : (A * D⁻¹).map star = (A * D⁻¹)ᴴ := by
    rw [conjTranspose, hsym]
  have hDh1 : (D⁻¹)ᴴ * Dᴴ = 1 := by rw [← conjTranspose_mul, hDi, conjTranspose_one]
  have main : A * D⁻¹ - (A * D⁻¹)ᴴ = (D⁻¹)ᴴ * (T - Tᴴ) * D⁻¹ := by
    rw [← kH]
    calc A * D⁻¹ - (A * D⁻¹)ᴴ = (D⁻¹)ᴴ * Dᴴ * A * D⁻¹ - (D⁻¹)ᴴ * Aᴴ * (D * D⁻¹) := by
          rw [hDh1, hDi, Matrix.one_mul, Matrix.mul_one, conjTranspose_mul]
      _ = (D⁻¹)ᴴ * (Dᴴ * A - Aᴴ * D) * D⁻¹ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have h2I : (2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  rw [hm]
  apply smul_right_injective _ h2I
  simp only
  rw [← hIm, hmapM, main, ← hmapT, hIm, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.SiegelMoeb
