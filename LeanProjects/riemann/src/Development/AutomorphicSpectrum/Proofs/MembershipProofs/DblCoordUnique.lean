import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.LagrangianStabilizerCharacterTrivial

open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal

namespace GlobalTheory.CompanionTheory.WeilOneMember

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem isHerm_dbl {JB : Matrix β β E} (h : IsHerm c JB) : IsHerm c (dbl JB) := by
  obtain ⟨hs, hu⟩ := h
  refine ⟨?_, ?_⟩
  · rintro (i | i) (j | j) <;> simp [dbl, hs]
  · rw [dbl, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact hu.mul ((isUnit_neg_one.pow _).mul hu)

theorem exists_embed {JB : Matrix β β E} (g : UG c JB) : ∃ gd : UG c (dbl JB),
    ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by
  let G : GL β E := g
  let M : GL (β ⊕ β) E :=
    ⟨Matrix.fromBlocks (G : Matrix β β E) 0 0 1, Matrix.fromBlocks ((G⁻¹ : GL β E) : Matrix β β E) 0 0 1,
      by simp [Matrix.fromBlocks_multiply], by simp [Matrix.fromBlocks_multiply]⟩
  have hg : (G : Matrix β β E).transpose * JB * (G : Matrix β β E).map c = JB := g.2
  have hM : M ∈ UG c (dbl JB) := by
    show (M : Matrix (β ⊕ β) (β ⊕ β) E).transpose * dbl JB * (M : Matrix (β ⊕ β) (β ⊕ β) E).map c = dbl JB
    simp only [M, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.transpose_zero, Matrix.transpose_one, Matrix.map_zero _ (map_zero c), Matrix.map_one _ (map_zero c) (map_one c)]
    simp [hg]
  exact ⟨⟨M, hM⟩, rfl⟩

end Alg

theorem boxFun_mem {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {κ κ' : Type}
    {φ₁ : (κ → R) → ℂ} {φ₂ : (κ' → R) → ℂ} (h₁ : φ₁ ∈ SB (κ → R)) (h₂ : φ₂ ∈ SB (κ' → R)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → R) := by
  have h₁' : IsLocallyConstant φ₁ ∧ HasCompactSupport φ₁ := h₁
  have h₂' : IsLocallyConstant φ₂ ∧ HasCompactSupport φ₂ := h₂
  have cl : Continuous fun x : κ ⊕ κ' → R => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → R => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  show IsLocallyConstant (boxFun φ₁ φ₂) ∧ HasCompactSupport (boxFun φ₁ φ₂)
  refine ⟨?_, ?_⟩
  · exact IsLocallyConstant.comp₂ (h₁'.1.comp_continuous cl) (h₂'.1.comp_continuous cr) (· * ·)
  · let S : Set (κ ⊕ κ' → R) :=
      (fun x => x ∘ Sum.inl) ⁻¹' tsupport φ₁ ∩ (fun x => x ∘ Sum.inr) ⁻¹' tsupport φ₂
    let gm : (κ → R) × (κ' → R) → (κ ⊕ κ' → R) := fun p => Sum.elim p.1 p.2
    have hgm : Continuous gm := by
      refine continuous_pi fun i => ?_
      cases i with
      | inl i => exact (continuous_apply i).comp continuous_fst
      | inr i => exact (continuous_apply i).comp continuous_snd
    have hK : IsCompact (gm '' (tsupport φ₁ ×ˢ tsupport φ₂)) := (h₁'.2.prod h₂'.2).image hgm
    have hSc : IsClosed S := (isClosed_tsupport φ₁).preimage cl |>.inter ((isClosed_tsupport φ₂).preimage cr)
    have hsub : tsupport (boxFun φ₁ φ₂) ⊆ S := by
      refine closure_minimal ?_ hSc
      intro x hx
      have hx' : φ₁ (x ∘ Sum.inl) * φ₂ (x ∘ Sum.inr) ≠ 0 := hx
      exact ⟨subset_tsupport _ (left_ne_zero_of_mul hx'), subset_tsupport _ (right_ne_zero_of_mul hx')⟩
    have hSK : S ⊆ gm '' (tsupport φ₁ ×ˢ tsupport φ₂) := by
      intro x hx
      exact ⟨(x ∘ Sum.inl, x ∘ Sum.inr), hx, Sum.elim_comp_inl_inr x⟩
    exact hK.of_isClosed_subset (isClosed_tsupport _) (hsub.trans hSK)

end GlobalTheory.CompanionTheory.WeilOneMember
