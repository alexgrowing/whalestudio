import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameOfFst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SWLagTerms.LagrangianFrames

section Blocks

variable {K : Type} [Field K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem row_rel (G : Matrix n n K) (hG : G.det ≠ 0) (B : Matrix (n ⊕ n) (n ⊕ n) K)
    (hB : Bᴴ * fromBlocks G 0 0 (-G) * B = fromBlocks G 0 0 (-G)) :
    B * fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ = fromBlocks G⁻¹ 0 0 (-G⁻¹) := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  have h1 : fromBlocks G 0 0 (-G) * fromBlocks G⁻¹ 0 0 (-G⁻¹) = 1 := by
    rw [fromBlocks_multiply]; simp [Matrix.mul_nonsing_inv _ hu, fromBlocks_one]
  have h2 : fromBlocks G⁻¹ 0 0 (-G⁻¹) * fromBlocks G 0 0 (-G) = 1 := by
    rw [fromBlocks_multiply]; simp [Matrix.nonsing_inv_mul _ hu, fromBlocks_one]
  have hL : (fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ * fromBlocks G 0 0 (-G)) * B = 1 := by
    calc (fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ * fromBlocks G 0 0 (-G)) * B
        = fromBlocks G⁻¹ 0 0 (-G⁻¹) * (Bᴴ * fromBlocks G 0 0 (-G) * B) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hB, h2]
  have hR : B * (fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ * fromBlocks G 0 0 (-G)) = 1 := mul_eq_one_comm.1 hL
  calc B * fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ
      = B * (fromBlocks G⁻¹ 0 0 (-G⁻¹) * Bᴴ * fromBlocks G 0 0 (-G)) * fromBlocks G⁻¹ 0 0 (-G⁻¹) := by
        simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
    _ = fromBlocks G⁻¹ 0 0 (-G⁻¹) := by rw [hR, Matrix.one_mul]

theorem blocks_rel (G : Matrix n n K) (hG : G.det ≠ 0) (B : Matrix (n ⊕ n) (n ⊕ n) K)
    (hB : Bᴴ * fromBlocks G 0 0 (-G) * B = fromBlocks G 0 0 (-G)) :
    B.toBlocks₁₁ * G⁻¹ * B.toBlocks₁₁ᴴ - B.toBlocks₁₂ * G⁻¹ * B.toBlocks₁₂ᴴ = G⁻¹ ∧
    B.toBlocks₁₁ * G⁻¹ * B.toBlocks₂₁ᴴ - B.toBlocks₁₂ * G⁻¹ * B.toBlocks₂₂ᴴ = 0 ∧
    B.toBlocks₂₁ * G⁻¹ * B.toBlocks₁₁ᴴ - B.toBlocks₂₂ * G⁻¹ * B.toBlocks₁₂ᴴ = 0 ∧
    B.toBlocks₂₁ * G⁻¹ * B.toBlocks₂₁ᴴ - B.toBlocks₂₂ * G⁻¹ * B.toBlocks₂₂ᴴ = -G⁻¹ := by
  have h := row_rel G hG B hB
  rw [← fromBlocks_toBlocks B, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at h
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, zero_sub, ← sub_eq_add_neg] at h
  exact h

end Blocks

section Blocks2

variable {K : Type} [Field K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem form_eq (G : Matrix n n K) (hG : G.det ≠ 0) (B : Matrix (n ⊕ n) (n ⊕ n) K)
    (hB : Bᴴ * fromBlocks G 0 0 (-G) * B = fromBlocks G 0 0 (-G)) :
    (B.toBlocks₁₁ - B.toBlocks₂₁) * G⁻¹ * (B.toBlocks₁₁ - B.toBlocks₂₁)ᴴ =
      (B.toBlocks₂₂ - B.toBlocks₁₂) * G⁻¹ * (B.toBlocks₂₂ - B.toBlocks₁₂)ᴴ := by
  obtain ⟨h11, h12, h21, h22⟩ := blocks_rel G hG B hB
  set a := B.toBlocks₁₁
  set b := B.toBlocks₁₂
  set c := B.toBlocks₂₁
  set d := B.toBlocks₂₂
  rw [← sub_eq_zero, Matrix.conjTranspose_sub, Matrix.conjTranspose_sub]
  have : (a - c) * G⁻¹ * (aᴴ - cᴴ) - (d - b) * G⁻¹ * (dᴴ - bᴴ) =
      (a * G⁻¹ * aᴴ - b * G⁻¹ * bᴴ) + (c * G⁻¹ * cᴴ - d * G⁻¹ * dᴴ) - (a * G⁻¹ * cᴴ - b * G⁻¹ * dᴴ) -
        (c * G⁻¹ * aᴴ - d * G⁻¹ * bᴴ) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [this, h11, h12, h21, h22]; abel

theorem adj_form (G : Matrix n n K) (hG : G.det ≠ 0) (hH : Gᴴ = G) (M : Matrix n n K) :
    (G⁻¹ * Mᴴ * G)ᴴ * G * (G⁻¹ * Mᴴ * G) = G * (M * G⁻¹ * Mᴴ) * G := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv, hH,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]

theorem ker_trivial (G : Matrix n n K) (hG : G.det ≠ 0) (B : Matrix (n ⊕ n) (n ⊕ n) K)
    (hB : Bᴴ * fromBlocks G 0 0 (-G) * B = fromBlocks G 0 0 (-G)) (v : n → K)
    (h1 : (G⁻¹ * (B.toBlocks₂₂ - B.toBlocks₁₂)ᴴ * G) *ᵥ v = 0)
    (h2 : (G⁻¹ * (B.toBlocks₁₁ - B.toBlocks₂₁)ᴴ * G) *ᵥ v = 0) : v = 0 := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  have hrow := row_rel G hG B hB
  set w := G *ᵥ v
  have k1 : (B.toBlocks₂₂ - B.toBlocks₁₂)ᴴ *ᵥ w = 0 := by
    have := congrArg (G *ᵥ ·) h1
    simpa [w, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu] using this
  have k2 : (B.toBlocks₁₁ - B.toBlocks₂₁)ᴴ *ᵥ w = 0 := by
    have := congrArg (G *ᵥ ·) h2
    simpa [w, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu] using this
  have hx : Bᴴ *ᵥ Sum.elim w (-w) = 0 := by
    rw [← fromBlocks_toBlocks B, fromBlocks_conjTranspose, fromBlocks_mulVec]
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mulVec] at k1 k2
    ext (i | i)
    · have := congrFun k2 i
      simp only [Pi.sub_apply, Pi.zero_apply] at this
      simp only [Sum.elim_inl, Pi.zero_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_neg, Pi.add_apply,
        Pi.neg_apply]
      linear_combination this
    · have := congrFun k1 i
      simp only [Pi.sub_apply, Pi.zero_apply] at this
      simp only [Sum.elim_inr, Pi.zero_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_neg, Pi.add_apply,
        Pi.neg_apply]
      linear_combination -this
  have hK : fromBlocks G⁻¹ 0 0 (-G⁻¹) *ᵥ Sum.elim w (-w) = 0 := by
    rw [← hrow, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have hw : w = 0 := by
    have := congrArg (fun x => fromBlocks G 0 0 (-G) *ᵥ x) hK
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero, fromBlocks_multiply] at this
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
      Matrix.mul_nonsing_inv _ hu, neg_zero, fromBlocks_one, Matrix.one_mulVec] at this
    funext i; exact congrFun this (Sum.inl i)
  have : G⁻¹ *ᵥ w = v := by simp [w, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu]
  rw [← this, hw, Matrix.mulVec_zero]

end Blocks2

variable {D : D7}

theorem unitary_of_mt (W : HSp D) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E)
    (h : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D)) :
    g₀ᴴ * (GlobalTheory.Doubling.dblSp W).gram * g₀ = (GlobalTheory.Doubling.dblSp W).gram := by
  have hγ : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ) *
      (GlobalTheory.Doubling.dblSp W).gram.map (incA D) * Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ =
      (GlobalTheory.Doubling.dblSp W).gram.map (incA D) := γ.2
  have hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g₀.map (incA D)) = g₀ᴴ.map (incA D) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    simp [sigR, CMData.sig, inclR]; rfl
  rw [h, hc, ← Matrix.map_mul, ← Matrix.map_mul] at hγ
  exact Matrix.map_injective
    (Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)) hγ

theorem star_dot' (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (x x' : Fin W.rank → D.host.E) :
    star (c *ᵥ x) ⬝ᵥ W.gram *ᵥ (c *ᵥ x') = star x ⬝ᵥ (cᴴ * W.gram * c) *ᵥ x' := by
  rw [Matrix.star_mulVec]
  conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

theorem blk_unitary (W : HSp D) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E)
    (h : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D)) :
    (blk W g₀)ᴴ * fromBlocks W.gram 0 0 (-W.gram) * blk W g₀ = fromBlocks W.gram 0 0 (-W.gram) := by
  have hU := unitary_of_mt W γ g₀ h
  rw [show (GlobalTheory.Doubling.dblSp W).gram = GlobalTheory.Doubling.dblGram finSumFinEquiv W.gram from GlobalTheory.Doubling.gram_hdbl W]
    at hU
  have := congrArg (fun X => X.submatrix finSumFinEquiv finSumFinEquiv) hU
  simp only [← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv _, Matrix.conjTranspose_submatrix,
    GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.submatrix_blkMat] at this
  exact this

theorem exists_lag_isLagFrame_frameOf (D : D7) (W : HSp D) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) → ∃ Y : Lag W, IsLagFrame W Y (frameOf W g₀) := by
  intro h
  have hB := blk_unitary W γ g₀ h
  have hG : (HSpace.gram W).det ≠ 0 := Formalism.L2.Theta.gram_det_ne W
  have hH : (HSpace.gram W)ᴴ = HSpace.gram W := Matrix.ext fun i j => W.herm.eq _ _
  set C := frameOf W g₀ with hC
  have h1 : C.1 = (HSpace.gram W)⁻¹ * ((blk W g₀).toBlocks₂₂ - (blk W g₀).toBlocks₁₂)ᴴ * HSpace.gram W := rfl
  have h2 : C.2 = (HSpace.gram W)⁻¹ * ((blk W g₀).toBlocks₁₁ - (blk W g₀).toBlocks₂₁)ᴴ * HSpace.gram W := rfl
  let φ : (Fin W.rank → D.host.E) →ₗ[D.host.E] (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E) :=
    LinearMap.prod (Matrix.mulVecLin C.1) (Matrix.mulVecLin C.2)
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun v hv => ?_
    have e1 : C.1 *ᵥ v = 0 := congrArg Prod.fst hv
    have e2 : C.2 *ᵥ v = 0 := congrArg Prod.snd hv
    rw [h1] at e1
    rw [h2] at e2
    exact ker_trivial _ hG _ hB v e1 e2
  let Y : Lag W := ⟨LinearMap.range φ, by
    rw [LinearMap.finrank_range_of_inj hinj]
    simp, by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    show star (C.1 *ᵥ x) ⬝ᵥ W.gram *ᵥ (C.1 *ᵥ y) = star (C.2 *ᵥ x) ⬝ᵥ W.gram *ᵥ (C.2 *ᵥ y)
    rw [star_dot', star_dot', h1, h2, adj_form _ hG hH, adj_form _ hG hH, form_eq _ hG _ hB]⟩
  refine ⟨Y, ?_⟩
  have hs := congrArg (Submodule.map φ) (Pi.basisFun D.host.E (Fin W.rank)).span_eq
  rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp] at hs
  refine Eq.trans ?_ hs
  congr 2
  funext j
  ext a <;> simp [φ, Matrix.mulVec, dotProduct, Pi.single_apply]

end GlobalTheory.SWLagTerms.LagrangianFrames
