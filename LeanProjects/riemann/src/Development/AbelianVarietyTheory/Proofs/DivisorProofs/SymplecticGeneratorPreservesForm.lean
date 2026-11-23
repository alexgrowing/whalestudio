import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne

open scoped Matrix

namespace GlobalTheory.AdelicSvN

def sympForm {F : Type} [Field F] {κ : Type} [Fintype κ] (v w : κ ⊕ κ → F) : F :=
  (v ∘ Sum.inl) ⬝ᵥ (w ∘ Sum.inr) - (w ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr)

theorem fromBlocks_mulVec_inl {F : Type} [Field F] {κ : Type} [Fintype κ]
    (A B C D : Matrix κ κ F) (v : κ ⊕ κ → F) :
    (Matrix.fromBlocks A B C D *ᵥ v) ∘ Sum.inl = A *ᵥ (v ∘ Sum.inl) + B *ᵥ (v ∘ Sum.inr) := by
  rw [Matrix.fromBlocks_mulVec]; rfl

theorem fromBlocks_mulVec_inr {F : Type} [Field F] {κ : Type} [Fintype κ]
    (A B C D : Matrix κ κ F) (v : κ ⊕ κ → F) :
    (Matrix.fromBlocks A B C D *ᵥ v) ∘ Sum.inr = C *ᵥ (v ∘ Sum.inl) + D *ᵥ (v ∘ Sum.inr) := by
  rw [Matrix.fromBlocks_mulVec]; rfl

theorem sympForm_gen {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (hg : g ∈ gens F κ) (v w : κ ⊕ κ → F) :
    sympForm (g *ᵥ v) (g *ᵥ w) = sympForm v w := by
  rcases hg with (⟨A, hA, rfl⟩ | ⟨C, hC, rfl⟩) | hW
  · simp only [sympForm, fromBlocks_mulVec_inl, fromBlocks_mulVec_inr, Matrix.zero_mulVec, add_zero, zero_add]
    have key : ∀ x y : κ → F, (A *ᵥ x) ⬝ᵥ ((A⁻¹)ᵀ *ᵥ y) = x ⬝ᵥ y := by
      intro x y
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]
    rw [key, key]
  · simp only [sympForm, fromBlocks_mulVec_inl, fromBlocks_mulVec_inr, Matrix.zero_mulVec, add_zero,
      Matrix.one_mulVec, Matrix.neg_mulVec]
    have key : ∀ x y : κ → F, x ⬝ᵥ (C *ᵥ y) = y ⬝ᵥ (C *ᵥ x) := by
      intro x y
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hC, dotProduct_comm]
    simp only [dotProduct_add, dotProduct_neg]
    rw [key (v ∘ Sum.inl) (w ∘ Sum.inl)]
    ring
  · rw [Set.mem_singleton_iff] at hW
    subst hW
    simp only [sympForm, fromBlocks_mulVec_inl, fromBlocks_mulVec_inr, Matrix.zero_mulVec, add_zero, zero_add,
      Matrix.one_mulVec, Matrix.neg_mulVec, dotProduct_neg]
    rw [dotProduct_comm (v ∘ Sum.inr), dotProduct_comm (w ∘ Sum.inr)]
    ring

theorem sympForm_nondeg {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (v : κ ⊕ κ → F) (h : ∀ w, sympForm v w = 0) : v = 0 := by
  funext j
  rcases j with i | i
  · have := h (Pi.single (Sum.inr i) 1)
    simpa [sympForm, Function.comp_def, Pi.single_apply, dotProduct] using this
  · have := h (Pi.single (Sum.inl i) 1)
    simpa [sympForm, Function.comp_def, Pi.single_apply, dotProduct] using this

theorem closure_gens_symp (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ]
    (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (hg : g ∈ Submonoid.closure (gens F κ)) :
    (∀ v w : κ ⊕ κ → F, ((g *ᵥ v) ∘ Sum.inl) ⬝ᵥ ((g *ᵥ w) ∘ Sum.inr) - ((g *ᵥ w) ∘ Sum.inl) ⬝ᵥ ((g *ᵥ v) ∘ Sum.inr) =
      (v ∘ Sum.inl) ⬝ᵥ (w ∘ Sum.inr) - (w ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr)) ∧ Function.Surjective fun v : κ ⊕ κ → F => g *ᵥ v := by
  have hf : ∀ v w : κ ⊕ κ → F, sympForm (g *ᵥ v) (g *ᵥ w) = sympForm v w := by
    induction hg using Submonoid.closure_induction with
    | mem x hx => exact sympForm_gen x hx
    | one => intro v w; simp
    | mul x y _ _ hx hy => intro v w; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, hy]
  refine ⟨hf, ?_⟩
  have hinj : Function.Injective fun v : κ ⊕ κ → F => g *ᵥ v := by
    intro v v' hvv
    have h0 : v - v' = 0 := by
      apply sympForm_nondeg
      intro w
      rw [← hf]
      simp only at hvv
      rw [Matrix.mulVec_sub, hvv, sub_self]
      simp [sympForm]
    exact sub_eq_zero.mp h0
  exact (Matrix.mulVec_surjective_iff_isUnit).mpr ((Matrix.mulVec_injective_iff_isUnit).mp hinj)

end GlobalTheory.AdelicSvN
