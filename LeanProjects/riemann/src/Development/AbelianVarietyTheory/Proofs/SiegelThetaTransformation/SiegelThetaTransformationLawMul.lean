import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.TransComp

theorem qm_mul {α β γ : Type} [Fintype β] (A : Matrix α β ℚ) (B : Matrix β γ ℚ) :
    qm (A * B) = qm A * qm B := by
  ext i j
  simp [qm, Matrix.mul_apply]

theorem qm_add {α β : Type} (A B : Matrix α β ℚ) : qm (A + B) = qm A + qm B := by
  ext i j
  simp [qm]

theorem qm_sub {α β : Type} (A B : Matrix α β ℚ) : qm (A - B) = qm A - qm B := by
  ext i j
  simp [qm]

theorem qm_transpose {α β : Type} (A : Matrix α β ℚ) : qm Aᵀ = (qm A)ᵀ := rfl

theorem qm_zero {α β : Type} : qm (0 : Matrix α β ℚ) = 0 := by
  ext i j
  simp [qm]

theorem qm_one {α : Type} [DecidableEq α] : qm (1 : Matrix α α ℚ) = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [qm, Matrix.one_apply, hij]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem blocks {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (h : σ ∈ Matrix.symplecticGroup ι ℚ) :
    σ.toBlocks₂₁ᵀ * σ.toBlocks₁₁ - σ.toBlocks₁₁ᵀ * σ.toBlocks₂₁ = 0 ∧
      σ.toBlocks₂₂ᵀ * σ.toBlocks₁₁ - σ.toBlocks₁₂ᵀ * σ.toBlocks₂₁ = 1 := by
  have h' := h
  rw [← Matrix.fromBlocks_toBlocks σ] at h'
  obtain ⟨h1, -, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 h'
  refine ⟨sub_eq_zero.2 h1.symm, ?_⟩

  have h4 := congrArg Matrix.transpose h3
  simpa [Matrix.transpose_sub, Matrix.transpose_mul] using h4

theorem mul_block (σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) :
    (σ' * σ).toBlocks₂₁ = σ'.toBlocks₂₁ * σ.toBlocks₁₁ + σ'.toBlocks₂₂ * σ.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.mul_apply,
    Fintype.sum_sum_type]

theorem key {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (h : σ ∈ Matrix.symplecticGroup ι ℚ)
    {τ : Matrix ι ι ℂ} (hτ : τ.IsSymm) (hd : (spDen σ τ).det ≠ 0) (hs : (spAct σ τ).IsSymm) :
    qm σ.toBlocks₁₁ = spAct σ τ * qm σ.toBlocks₂₁ + ((spDen σ τ)⁻¹)ᵀ := by
  have hu : IsUnit (spDen σ τ).det := isUnit_iff_ne_zero.mpr hd

  have h1 : (spDen σ τ)ᵀ * spAct σ τ = (qm σ.toBlocks₁₁ * τ + qm σ.toBlocks₁₂)ᵀ := by
    have hs' : (spAct σ τ)ᵀ = spAct σ τ := hs
    rw [← hs']
    unfold spAct
    rw [Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ hu, Matrix.transpose_one, Matrix.one_mul]
  have hτ' : τᵀ = τ := hτ
  obtain ⟨b1, b2⟩ := blocks h
  have e1 := congrArg qm b1
  have e2 := congrArg qm b2
  rw [qm_sub, qm_mul, qm_mul, qm_transpose, qm_transpose, qm_zero] at e1
  rw [qm_sub, qm_mul, qm_mul, qm_transpose, qm_transpose, qm_one] at e2
  have h2 : (spDen σ τ)ᵀ * (qm σ.toBlocks₁₁ - spAct σ τ * qm σ.toBlocks₂₁) = 1 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h1]
    unfold spDen
    rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      hτ']
    calc (τ * (qm σ.toBlocks₂₁)ᵀ + (qm σ.toBlocks₂₂)ᵀ) * qm σ.toBlocks₁₁ -
          (τ * (qm σ.toBlocks₁₁)ᵀ + (qm σ.toBlocks₁₂)ᵀ) * qm σ.toBlocks₂₁
        = τ * ((qm σ.toBlocks₂₁)ᵀ * qm σ.toBlocks₁₁ - (qm σ.toBlocks₁₁)ᵀ * qm σ.toBlocks₂₁) +
          ((qm σ.toBlocks₂₂)ᵀ * qm σ.toBlocks₁₁ - (qm σ.toBlocks₁₂)ᵀ * qm σ.toBlocks₂₁) := by
          noncomm_ring
      _ = 1 := by rw [e1, e2, Matrix.mul_zero, zero_add]
  rw [Matrix.transpose_nonsing_inv, Matrix.inv_eq_right_inv h2]
  abel

end GlobalTheory.SW.TransComp

open GlobalTheory.SW.TransComp in

theorem GlobalTheory.SW.transS_comp : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → σ' ∈ Matrix.symplecticGroup ι ℚ → ∀ φ ψ χ : Matrix κ ι ℚ → ℂ, TransS σ φ ψ → TransS σ' ψ χ → TransS (σ' * σ) φ χ := by
  intro κ ι _ _ _ σ σ' hσ hσ' φ ψ χ h1 h2 τ hτ ζ
  obtain ⟨hd, hmem, -, -, hcomp⟩ := GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle ι σ hσ τ hτ
  obtain ⟨hden, hact⟩ := hcomp σ' hσ'
  have hd' := (GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle ι σ' hσ' _ hmem).1
  rw [hden, hact]

  have hk := key hσ hτ.1 hd hmem.1
  have hD' : qm σ'.toBlocks₂₂ = spDen σ' (spAct σ τ) - qm σ'.toBlocks₂₁ * spAct σ τ := by
    rw [spDen, add_sub_cancel_left]
  have hinv' : (spDen σ' (spAct σ τ))⁻¹ * spDen σ' (spAct σ τ) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd')

  have hM : (spDen σ τ)⁻¹ * ((spDen σ' (spAct σ τ))⁻¹ * qm σ'.toBlocks₂₁) * ((spDen σ τ)⁻¹)ᵀ +
      (spDen σ τ)⁻¹ * qm σ.toBlocks₂₁ =
      (spDen σ' (spAct σ τ) * spDen σ τ)⁻¹ * qm (σ' * σ).toBlocks₂₁ := by
    rw [mul_block, qm_add, qm_mul, qm_mul, hk, hD', Matrix.mul_inv_rev]
    have inner : qm σ'.toBlocks₂₁ * (spAct σ τ * qm σ.toBlocks₂₁ + ((spDen σ τ)⁻¹)ᵀ) +
        (spDen σ' (spAct σ τ) - qm σ'.toBlocks₂₁ * spAct σ τ) * qm σ.toBlocks₂₁ =
        qm σ'.toBlocks₂₁ * ((spDen σ τ)⁻¹)ᵀ + spDen σ' (spAct σ τ) * qm σ.toBlocks₂₁ := by
      noncomm_ring
    rw [inner, Matrix.mul_add, Matrix.mul_assoc (spDen σ τ)⁻¹ (spDen σ' (spAct σ τ))⁻¹,
      Matrix.mul_assoc (spDen σ τ)⁻¹ (spDen σ' (spAct σ τ))⁻¹, ← Matrix.mul_assoc
      (spDen σ' (spAct σ τ))⁻¹ (spDen σ' (spAct σ τ)), hinv', Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  have hq : ∀ v : ι → ℂ, v ⬝ᵥ ((spDen σ' (spAct σ τ) * spDen σ τ)⁻¹ * qm (σ' * σ).toBlocks₂₁) *ᵥ v =
      (v ᵥ* (spDen σ τ)⁻¹) ⬝ᵥ ((spDen σ' (spAct σ τ))⁻¹ * qm σ'.toBlocks₂₁) *ᵥ (v ᵥ* (spDen σ τ)⁻¹) +
        v ⬝ᵥ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁) *ᵥ v := by
    intro v
    rw [← hM, Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have hfun : (fun k => ζ k ᵥ* (spDen σ' (spAct σ τ) * spDen σ τ)⁻¹) =
      fun k => (ζ k ᵥ* (spDen σ τ)⁻¹) ᵥ* (spDen σ' (spAct σ τ))⁻¹ := by
    funext k
    rw [Matrix.mul_inv_rev, Matrix.vecMul_vecMul]
  rw [hfun, h2 _ hmem, h1 τ hτ ζ, Matrix.det_mul, mul_pow]
  simp only [hq, Finset.sum_add_distrib, mul_add, Complex.exp_add]
  ring
