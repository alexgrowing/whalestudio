import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarIsomG

noncomputable section

open scoped Classical
open Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

open Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem lm_conjTranspose {N : ℕ} (A : Matrix (Fin N) (Fin N) E) (l : ℕ) :
    leadMinorE Aᴴ l = star (leadMinorE A l) := by
  unfold leadMinorE
  split_ifs with h
  · rw [← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]
  · simp

theorem eq_of_mulVec_last {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hA : A.det ≠ 0) (x : Fin (r + 1) → E)
    (c : E) (h : A *ᵥ x = c • Pi.single (Fin.last r) 1) :
    x = (c / A.det) • fun b => A.adjugate b (Fin.last r) := by
  have hx : x = A⁻¹ *ᵥ (c • Pi.single (Fin.last r) 1) := by
    rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]
  rw [hx, Matrix.inv_def, Ring.inverse_eq_inv']
  ext b
  simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.single_apply, div_eq_inv_mul]
  ring

theorem gram_pair_det {r : ℕ} {T T' : E} (F : FlagG S r T) (f₁ : Fin (r + 1) → S.V)
    (h1 : ∀ a b, (a ≠ Fin.last r ∨ b ≠ Fin.last r) → S.hT (f₁ a) (f₁ b) = 0)
    (h2 : S.hT (f₁ (Fin.last r)) (f₁ (Fin.last r)) = -T')
    (hZ₁ : (gram S f₁ F.fvec).det ≠ 0)
    (hG : (gram S f₁ F.fvec).det * star (gram S f₁ F.fvec).det -
      T * T' * (leadMinorE (gram S f₁ F.fvec) r * star (leadMinorE (gram S f₁ F.fvec) r)) ≠ 0) :
    (gram S (Sum.elim F.fvec f₁) (Sum.elim F.fvec f₁)).det ≠ 0 := by
  set f := F.fvec with hf
  set Z₁ := gram S f₁ f with hZ₁d
  set l := Fin.last r with hl
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set α : Fin (r + 1) → E := fun a => v (Sum.inl a) with hα
  set β : Fin (r + 1) → E := fun b => v (Sum.inr b) with hβ
  have hrow : ∀ k, ∑ a, S.hT (Sum.elim f f₁ k) (f a) * α a + ∑ b, S.hT (Sum.elim f f₁ k) (f₁ b) * β b = 0 := by
    intro k
    have := congrFun hv k
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, gram, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply] at this
    exact this
  have hΓ : ∀ a' (x : Fin (r + 1) → E), ∑ a, S.hT (f a') (f a) * x a = if a' = l then -T * x l else 0 := by
    intro a' x
    rw [Finset.sum_eq_single l]
    · split_ifs with h
      · subst h; rw [show S.hT (f l) (f l) = -T from gram_fvec_last F]
      · rw [show S.hT (f a') (f l) = 0 from gram_fvec_zero F _ _ (Or.inl h), zero_mul]
    · intro a _ ha; rw [show S.hT (f a') (f a) = 0 from gram_fvec_zero F _ _ (Or.inr ha), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hΓ' : ∀ b' (x : Fin (r + 1) → E), ∑ b, S.hT (f₁ b') (f₁ b) * x b = if b' = l then -T' * x l else 0 := by
    intro b' x
    rw [Finset.sum_eq_single l]
    · split_ifs with h
      · subst h; rw [h2]
      · rw [h1 _ _ (Or.inl h), zero_mul]
    · intro b _ hb; rw [h1 _ _ (Or.inr hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hZβ : Z₁ *ᵥ β = (T * α l) • Pi.single l 1 := by
    ext a'
    have e := hrow (Sum.inl a')
    simp only [Sum.elim_inl, hΓ] at e
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.single_apply, smul_eq_mul, hZ₁d, gram]
    split_ifs at e ⊢ with h
    · linear_combination e
    · linear_combination e
  have hZα : Z₁ᴴ *ᵥ α = (T' * β l) • Pi.single l 1 := by
    ext b'
    have e := hrow (Sum.inr b')
    simp only [Sum.elim_inr, hΓ'] at e
    have hc : ∀ a, S.hT (f₁ b') (f a) = Z₁ᴴ b' a := fun a => by
      rw [Matrix.conjTranspose_apply, hZ₁d, gram, ← (LinearMap.isSymm_def.1 S.herm) (f₁ b') (f a),
        starRingEnd_apply, star_star]
    simp only [hc] at e
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs at e ⊢ with h
    · linear_combination e
    · linear_combination e
  have hZ₁h : Z₁ᴴ.det ≠ 0 := by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hZ₁
  have eβ := eq_of_mulVec_last Z₁ hZ₁ β _ hZβ
  have eα := eq_of_mulVec_last Z₁ᴴ hZ₁h α _ hZα
  have eβl : β l = T * α l / Z₁.det * leadMinorE Z₁ r := by
    have := congrFun eβ l
    rw [this, Pi.smul_apply, smul_eq_mul, adj_last]
  have eαl : α l = T' * β l / star Z₁.det * star (leadMinorE Z₁ r) := by
    have := congrFun eα l
    rw [this, Pi.smul_apply, smul_eq_mul, adj_last, lm_conjTranspose, Matrix.det_conjTranspose]
  have hsZ : star Z₁.det ≠ 0 := star_ne_zero.2 hZ₁
  have hαl : α l = 0 := by
    have key : α l * (Z₁.det * star Z₁.det - T * T' * (leadMinorE Z₁ r * star (leadMinorE Z₁ r))) = 0 := by
      rw [eβl] at eαl
      field_simp at eαl
      linear_combination eαl
    rcases mul_eq_zero.1 key with h | h
    · exact h
    · exact absurd h hG
  have hβ0 : β = 0 := by rw [eβ, hαl, mul_zero, zero_div, zero_smul]
  have hβl : β l = 0 := by rw [hβ0]; rfl
  have hα0 : α = 0 := by rw [eα, hβl, mul_zero, zero_div, zero_smul]
  apply hv0
  funext k
  rcases k with a | b
  · exact congrFun hα0 a
  · exact congrFun hβ0 b

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA
