import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.UnitaryMemGLs

noncomputable section

open Matrix Module

namespace PositivityTheory.RgBcC.VC.GFA

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

variable {n : ℕ}

theorem mulVec_eq_sum (g : Mat n) (c : Fin n → ℂ) : g *ᵥ c = ∑ j, c j • (fun i => g i j) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem adapted (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) :
    ∃ (g : Mat n) (blk : Fin n → ℕ), IsUnit g ∧ (∀ j, blk j ≤ 2) ∧
      (∀ c, g *ᵥ c ∈ W₁ ↔ ∀ j, blk j ≠ 0 → c j = 0) ∧ (∀ c, g *ᵥ c ∈ W₂ ↔ ∀ j, blk j = 2 → c j = 0) := by
  classical
  obtain ⟨b₁, hb₁, hspan₁, hli₁'⟩ := exists_linearIndependent ℂ (W₁ : Set (Fin n → ℂ))
  have hli₁ : LinearIndepOn ℂ id b₁ := hli₁'
  have hb₁₂ : b₁ ⊆ (W₂ : Set (Fin n → ℂ)) := hb₁.trans hW
  set b₂ := hli₁.extend hb₁₂ with hb₂def
  have hli₂ : LinearIndepOn ℂ id b₂ := hli₁.linearIndepOn_extend hb₁₂
  have hb₂W : b₂ ⊆ (W₂ : Set (Fin n → ℂ)) := hli₁.extend_subset hb₁₂
  have h12 : b₁ ⊆ b₂ := hli₁.subset_extend hb₁₂
  have hW₂s : (W₂ : Set (Fin n → ℂ)) ⊆ Submodule.span ℂ b₂ := hli₁.subset_span_extend hb₁₂
  set B := Module.Basis.extend hli₂ with hBdef
  have h23 : b₂ ⊆ Set.range B := by rw [Module.Basis.range_extend]; exact hli₂.subset_extend _
  have : Finite (hli₂.extend (Set.subset_univ b₂)) := Module.Finite.finite_basis B
  haveI : Fintype (hli₂.extend (Set.subset_univ b₂)) := Fintype.ofFinite _
  have hcard : Fintype.card (hli₂.extend (Set.subset_univ b₂)) = n := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  set B' := B.reindex (Fintype.equivFinOfCardEq hcard) with hB'def
  have hrange : Set.range B' = Set.range B := by
    rw [hB'def, Module.Basis.coe_reindex]
    exact (Fintype.equivFinOfCardEq hcard).symm.surjective.range_comp _
  refine ⟨Matrix.of fun i j => B' j i, fun j => if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2, ?_, ?_, ?_, ?_⟩
  · rw [← linearIndependent_cols_iff_isUnit]
    exact B'.linearIndependent
  · intro j; dsimp only; split_ifs <;> omega
  · intro c
    have e : (Matrix.of fun i j => B' j i) *ᵥ c = B'.equivFun.symm c := by
      rw [mulVec_eq_sum, Module.Basis.equivFun_symm_apply]; rfl
    have hr : ∀ j, B'.repr (B'.equivFun.symm c) j = c j := fun j => by
      have h0 := congrFun (B'.equivFun.apply_symm_apply c) j
      rwa [Module.Basis.equivFun_apply] at h0
    have hW₁ : W₁ = Submodule.span ℂ (B' '' {j | B' j ∈ b₁}) := by
      calc W₁ = Submodule.span ℂ (W₁ : Set (Fin n → ℂ)) := (Submodule.span_eq W₁).symm
        _ = Submodule.span ℂ b₁ := hspan₁.symm
        _ = _ := by
          congr 1
          ext v
          simp only [Set.mem_image, Set.mem_ofPred_eq]
          constructor
          · intro hv
            obtain ⟨j, hj⟩ : v ∈ Set.range B' := hrange ▸ h23 (h12 hv)
            exact ⟨j, hj ▸ hv, hj⟩
          · rintro ⟨j, hj, rfl⟩; exact hj
    rw [e, hW₁, Module.Basis.mem_span_image]
    constructor
    · intro h j hj
      by_contra hc
      have hm : j ∈ ((B'.repr (B'.equivFun.symm c)).support : Set (Fin n)) := by
        rw [Finset.mem_coe, Finsupp.mem_support_iff, hr]; exact hc
      have h' : B' j ∈ b₁ := h hm
      change (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) ≠ 0 at hj
      rw [if_pos h'] at hj
      exact hj rfl
    · intro h j hj
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hr] at hj
      show B' j ∈ b₁
      by_contra hb
      refine hj (h j ?_)
      show (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) ≠ 0
      rw [if_neg hb]; split_ifs <;> omega
  · intro c
    have e : (Matrix.of fun i j => B' j i) *ᵥ c = B'.equivFun.symm c := by
      rw [mulVec_eq_sum, Module.Basis.equivFun_symm_apply]; rfl
    have hr : ∀ j, B'.repr (B'.equivFun.symm c) j = c j := fun j => by
      have h0 := congrFun (B'.equivFun.apply_symm_apply c) j
      rwa [Module.Basis.equivFun_apply] at h0
    have hW₂ : W₂ = Submodule.span ℂ (B' '' {j | B' j ∈ b₂}) := by
      calc W₂ = Submodule.span ℂ b₂ :=
            le_antisymm (fun x hx => hW₂s hx) (Submodule.span_le.2 hb₂W)
        _ = _ := by
          congr 1
          ext v
          simp only [Set.mem_image, Set.mem_ofPred_eq]
          constructor
          · intro hv
            obtain ⟨j, hj⟩ : v ∈ Set.range B' := hrange ▸ h23 hv
            exact ⟨j, hj ▸ hv, hj⟩
          · rintro ⟨j, hj, rfl⟩; exact hj
    rw [e, hW₂, Module.Basis.mem_span_image]
    constructor
    · intro h j hj
      by_contra hc
      have hm : j ∈ ((B'.repr (B'.equivFun.symm c)).support : Set (Fin n)) := by
        rw [Finset.mem_coe, Finsupp.mem_support_iff, hr]; exact hc
      have h' : B' j ∈ b₂ := h hm
      change (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) = 2 at hj
      by_cases h1 : B' j ∈ b₁
      · rw [if_pos h1] at hj; exact absurd hj (by decide)
      · rw [if_neg h1, if_pos h'] at hj; exact absurd hj (by decide)
    · intro h j hj
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hr] at hj
      show B' j ∈ b₂
      by_contra hb
      have hb1 : B' j ∉ b₁ := fun h1 => hb (h12 h1)
      refine hj (h j ?_)
      show (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) = 2
      rw [if_neg hb1, if_neg hb]

end PositivityTheory.RgBcC.VC.GFA
