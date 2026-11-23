import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SiegelAction

open scoped ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem posDef_ofReal {Y : Matrix ι ι ℝ} (h : Y.PosDef) :
    (Y.map (fun t => (t : ℂ))).PosDef := by
  have hs : ∀ i j, Y i j = Y j i := fun i j => by
    have := congrFun (congrFun h.isHermitian j) i
    simpa using this
  have hH : (Y.map (fun t => (t : ℂ))).IsHermitian := by
    ext i j
    simp [hs i j]
  refine PosDef.of_dotProduct_mulVec_pos hH fun v hv => ?_
  have hre : (star v ⬝ᵥ (Y.map (fun t => (t : ℂ))) *ᵥ v).re =
      star (fun i => (v i).re) ⬝ᵥ Y *ᵥ (fun i => (v i).re) +
      star (fun i => (v i).im) ⬝ᵥ Y *ᵥ (fun i => (v i).im) := by
    simp [dotProduct, mulVec, Finset.mul_sum, Finset.sum_add_distrib]
  have him : (star v ⬝ᵥ (Y.map (fun t => (t : ℂ))) *ᵥ v).im = 0 := by
    have := hH.im_star_dotProduct_mulVec_self v
    simpa using this
  rw [Complex.pos_iff, hre, him]
  refine ⟨?_, rfl⟩
  by_cases h1 : (fun i => (v i).re) = 0
  · have h2 : (fun i => (v i).im) ≠ 0 := fun h2 => hv (by
      ext i
      exact Complex.ext (congrFun h1 i) (congrFun h2 i))
    exact add_pos_of_nonneg_of_pos (h.posSemidef.dotProduct_mulVec_nonneg _)
      (h.dotProduct_mulVec_pos h2)
  · exact add_pos_of_pos_of_nonneg (h.dotProduct_mulVec_pos h1)
      (h.posSemidef.dotProduct_mulVec_nonneg _)

omit [DecidableEq ι] in

theorem posDef_of_ofReal {Y : Matrix ι ι ℝ} (h : (Y.map (fun t => (t : ℂ))).PosDef) :
    Y.PosDef := by
  have hH : Y.IsHermitian := by
    ext i j
    have := congrFun (congrFun h.isHermitian i) j
    simpa using this
  refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have hv : (fun i => (x i : ℂ)) ≠ 0 := fun h0 => hx (by
    ext i
    simpa using congrFun h0 i)
  have := (Complex.pos_iff.1 (h.dotProduct_mulVec_pos hv)).1
  simpa [dotProduct, mulVec, Finset.mul_sum] using this

omit [Fintype ι] [DecidableEq ι] in
theorem sub_conj_eq (τ : Matrix ι ι ℂ) :
    τ - τ.map conj = (2 * I) • τ.map (fun z => (z.im : ℂ)) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Complex.sub_conj]
  push_cast
  ring

theorem block_identity {A B C D τ τ' : Matrix ι ι ℂ}
    (h : fromBlocks A B C D ∈ symplecticGroup ι ℂ) (hτ : τ.IsSymm) :
    (A * τ + B)ᵀ * (C * τ' + D) - (C * τ + D)ᵀ * (A * τ' + B) = τ - τ' := by
  obtain ⟨h1, h2, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 h
  have h4 : Dᵀ * A - Bᵀ * C = 1 := by simpa using congrArg transpose h3
  have : (A * τ + B)ᵀ * (C * τ' + D) - (C * τ + D)ᵀ * (A * τ' + B) =
      τ * (Aᵀ * C - Cᵀ * A) * τ' + τ * (Aᵀ * D - Cᵀ * B) - (Dᵀ * A - Bᵀ * C) * τ' +
        (Bᵀ * D - Dᵀ * B) := by
    simp only [transpose_add, transpose_mul, hτ.eq]
    noncomm_ring
  rw [this, h1, h2, h3, h4]
  simp

theorem act_complex {A B C D τ : Matrix ι ι ℂ}
    (h : fromBlocks A B C D ∈ symplecticGroup ι ℂ) (hA : A.map conj = A) (hB : B.map conj = B)
    (hC : C.map conj = C) (hD : D.map conj = D) (hτ : τ ∈ Siegel ι) :
    (C * τ + D).det ≠ 0 ∧ (A * τ + B) * (C * τ + D)⁻¹ ∈ Siegel ι ∧ ((C * τ + D)⁻¹ * C).IsSymm ∧
      (C * τ + D)ᵀ * ((A * τ + B) * (C * τ + D)⁻¹).map (fun z => (z.im : ℂ)) *
        (C * τ + D).map conj = τ.map (fun z => (z.im : ℂ)) := by
  obtain ⟨hs, hp⟩ := hτ
  have hY : (τ.map (fun z => (z.im : ℂ))).PosDef := posDef_ofReal hp
  have e1 := block_identity (τ' := τ) h hs
  have e2 := block_identity (τ' := τ.map conj) h hs
  have cP : (A * τ + B).map conj = A * τ.map conj + B := by
    rw [Matrix.map_add _ (map_add conj), Matrix.map_mul, hA, hB]
  have cQ : (C * τ + D).map conj = C * τ.map conj + D := by
    rw [Matrix.map_add _ (map_add conj), Matrix.map_mul, hC, hD]
  have e3 : C * (C * τ + D)ᵀ = (C * τ + D) * Cᵀ := by
    have ht := SymplecticGroup.transpose_mem h
    rw [fromBlocks_transpose] at ht
    obtain ⟨-, h2, -⟩ := SymplecticGroup.fromBlocks_mem_iff.1 ht
    simp only [transpose_transpose] at h2
    simp only [transpose_add, transpose_mul, hs.eq, Matrix.mul_add, Matrix.add_mul, h2,
      Matrix.mul_assoc]
  rw [← cP, ← cQ, sub_conj_eq] at e2
  rw [sub_self, sub_eq_zero] at e1
  generalize A * τ + B = P at *
  generalize C * τ + D = Q at *
  have h2I : (2 * I : ℂ) ≠ 0 := by simp
  have hQt : (Q.map conj)ᴴ = Qᵀ := by
    ext i j; simp
  have hdet : Q.det ≠ 0 := by
    intro h0
    have h0' : (Q.map conj).det = 0 := by
      have := RingHom.map_det (starRingEnd ℂ) Q
      rw [h0, map_zero] at this
      exact this.symm
    obtain ⟨v, hv, hQv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0'
    have hQv' : star v ᵥ* Qᵀ = 0 := by
      rw [← hQt, ← star_mulVec, hQv, star_zero]
    have hpos := hY.dotProduct_mulVec_pos hv
    have := congrArg (fun M => star v ⬝ᵥ M *ᵥ v) e2
    simp only [sub_mulVec, ← mulVec_mulVec, hQv, mulVec_zero, dotProduct_sub, dotProduct_zero,
      smul_mulVec, dotProduct_smul, smul_eq_mul] at this
    rw [dotProduct_mulVec (star v) Qᵀ, hQv', zero_dotProduct, sub_zero] at this
    exact hpos.ne' ((mul_eq_zero.1 this.symm).resolve_left h2I)
  have hu : IsUnit Q.det := hdet.isUnit
  have hut : IsUnit Qᵀ.det := by rwa [det_transpose]
  have hWQ : P * Q⁻¹ * Q = P := nonsing_inv_mul_cancel_right _ _ hu
  have hQW : Qᵀ * (P * Q⁻¹) = Pᵀ := by
    rw [← Matrix.mul_assoc, ← e1, mul_nonsing_inv_cancel_right _ _ hu]
  have hWs : (P * Q⁻¹).IsSymm := by
    rw [IsSymm, transpose_mul, transpose_nonsing_inv, ← hQW, nonsing_inv_mul_cancel_left _ _ hut]
  have hcW : (P * Q⁻¹).map conj * Q.map conj = P.map conj := by
    rw [← Matrix.map_mul, hWQ]
  have key : Qᵀ * (P * Q⁻¹).map (fun z => (z.im : ℂ)) * Q.map conj =
      τ.map (fun z => (z.im : ℂ)) := by
    apply smul_right_injective _ h2I
    simp only
    rw [← e2, ← Matrix.smul_mul, ← Matrix.mul_smul, ← sub_conj_eq, Matrix.mul_sub, Matrix.sub_mul,
      hQW, Matrix.mul_assoc Qᵀ, hcW]
  refine ⟨hdet, ⟨hWs, posDef_of_ofReal ?_⟩, ?_, key⟩
  · have huc : IsUnit (Q.map conj) := by
      rw [isUnit_iff_isUnit_det]
      have := RingHom.map_det (starRingEnd ℂ) Q
      exact this ▸ hu.map (starRingEnd ℂ)
    refine (Matrix.IsUnit.posDef_star_left_conjugate_iff huc).1 ?_
    rw [star_eq_conjTranspose, hQt]
    rw [← key] at hY
    exact hY
  · rw [IsSymm, transpose_mul, transpose_nonsing_inv]
    calc Cᵀ * Qᵀ⁻¹ = Q⁻¹ * (Q * Cᵀ) * Qᵀ⁻¹ := by rw [nonsing_inv_mul_cancel_left _ _ hu]
      _ = Q⁻¹ * C := by
        rw [← e3, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hut]

theorem qm_conj {α β : Type} (A : Matrix α β ℚ) : (qm A).map conj = qm A := by
  ext i j; simp [qm]

theorem qm_add {α β : Type} (A B : Matrix α β ℚ) : qm (A + B) = qm A + qm B := by
  ext i j; simp [qm]

theorem qm_mul {α β γ : Type} [Fintype β] (A : Matrix α β ℚ) (B : Matrix β γ ℚ) :
    qm (A * B) = qm A * qm B := by
  ext i j; simp [qm, Matrix.mul_apply]

theorem qm_blocks_mem {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (h : σ ∈ symplecticGroup ι ℚ) :
    fromBlocks (qm σ.toBlocks₁₁) (qm σ.toBlocks₁₂) (qm σ.toBlocks₂₁) (qm σ.toBlocks₂₂) ∈
      symplecticGroup ι ℂ := by
  have := SymplecticGroup.map_mem h (Rat.castHom ℂ)
  rw [← fromBlocks_toBlocks σ, fromBlocks_map] at this
  exact this

omit [DecidableEq ι] in
theorem toBlocks_mul (σ' σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) :
    (σ' * σ).toBlocks₁₁ = σ'.toBlocks₁₁ * σ.toBlocks₁₁ + σ'.toBlocks₁₂ * σ.toBlocks₂₁ ∧
    (σ' * σ).toBlocks₁₂ = σ'.toBlocks₁₁ * σ.toBlocks₁₂ + σ'.toBlocks₁₂ * σ.toBlocks₂₂ ∧
    (σ' * σ).toBlocks₂₁ = σ'.toBlocks₂₁ * σ.toBlocks₁₁ + σ'.toBlocks₂₂ * σ.toBlocks₂₁ ∧
    (σ' * σ).toBlocks₂₂ = σ'.toBlocks₂₁ * σ.toBlocks₁₂ + σ'.toBlocks₂₂ * σ.toBlocks₂₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply]

theorem symplectic_action : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ Siegel ι,
    (spDen σ τ).det ≠ 0 ∧ spAct σ τ ∈ Siegel ι ∧ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁).IsSymm ∧
    (spDen σ τ)ᵀ * (spAct σ τ).map (fun z => (z.im : ℂ)) * (spDen σ τ).map conj =
      τ.map (fun z => (z.im : ℂ)) ∧
    ∀ σ' ∈ Matrix.symplecticGroup ι ℚ, spDen (σ' * σ) τ = spDen σ' (spAct σ τ) * spDen σ τ ∧
      spAct (σ' * σ) τ = spAct σ' (spAct σ τ) := by
  intro ι _ _ σ hσ τ hτ
  obtain ⟨h1, h2, h3, h4⟩ := act_complex (qm_blocks_mem hσ) (qm_conj _) (qm_conj _) (qm_conj _)
    (qm_conj _) hτ
  refine ⟨h1, h2, h3, h4, fun σ' _ => ?_⟩
  have hu : IsUnit (spDen σ τ).det := h1.isUnit
  have hWQ : spAct σ τ * spDen σ τ = qm σ.toBlocks₁₁ * τ + qm σ.toBlocks₁₂ :=
    nonsing_inv_mul_cancel_right _ _ hu
  obtain ⟨m1, m2, m3, m4⟩ := toBlocks_mul σ' σ
  have gen : ∀ X Y : Matrix ι ι ℚ,
      qm (X * σ.toBlocks₁₁ + Y * σ.toBlocks₂₁) * τ + qm (X * σ.toBlocks₁₂ + Y * σ.toBlocks₂₂) =
        (qm X * spAct σ τ + qm Y) * spDen σ τ := by
    intro X Y
    rw [Matrix.add_mul (qm X * spAct σ τ), Matrix.mul_assoc, hWQ]
    simp only [qm_add, qm_mul, spDen]
    noncomm_ring
  have hden : spDen (σ' * σ) τ = spDen σ' (spAct σ τ) * spDen σ τ := by
    rw [spDen, m3, m4, gen]; rfl
  refine ⟨hden, ?_⟩
  rw [spAct, hden, m1, m2, gen, Matrix.mul_inv_rev, Matrix.mul_assoc,
    mul_nonsing_inv_cancel_left _ _ hu]
  rfl

end GlobalTheory.SiegelAction
