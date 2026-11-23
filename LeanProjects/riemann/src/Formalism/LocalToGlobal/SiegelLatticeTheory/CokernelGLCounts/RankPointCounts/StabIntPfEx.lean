import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfStG

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def CondX (w : Point D.host.E (D.R.rS + 1)) (X : MatR D) : Prop :=
  ∀ a c : Fin (D.R.rS + 1), a < c → blkOf w.1 a.val = blkOf w.1 c.val →
    X (pinv w c) (pinv w a) ∈ ddPow D (c.val - a.val) ∧ bt D X⁻¹ a c ∈ ddPow D (c.val - a.val) ∧
      X (pinv w c) (pinv w a) - D.conjF (bt D X⁻¹ a c) ∈ qdPow D (c.val - a.val)

theorem entryShape_iff (w : Point D.host.E (D.R.rS + 1)) {β b : MatR D} (hβ : IsLoUni β) (hb : IsUpUni b)
    (hW : β * ptMat w * b = ptMat w) :
    EntryShape D β b ↔ CondX w ((ptMat w)⁻¹ * β * ptMat w) := by
  obtain ⟨hXb, hX, hXB⟩ := X_of_st w hβ hb hW
  set X := (ptMat w)⁻¹ * β * ptMat w with hXdef
  have hbX : b = X⁻¹ := by
    rw [hXb, Matrix.nonsing_inv_nonsing_inv _ (by rw [upU_det hb]; exact isUnit_one)]

  have hβX : β = ptMat w * X * (ptMat w)⁻¹ := by
    have hu := ptMat_isUnit w
    rw [hXdef, show ptMat w * ((ptMat w)⁻¹ * β * ptMat w) * (ptMat w)⁻¹ =
      (ptMat w * (ptMat w)⁻¹) * β * (ptMat w * (ptMat w)⁻¹) by simp only [Matrix.mul_assoc],
      Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]
  have hβij : ∀ i j, β i j = cv w i * X (pinv w i) (pinv w j) * (cv w j)⁻¹ := by
    intro i j; rw [hβX, conj'_apply]

  have hXiB : IsBlockDiagonalMatrix w X⁻¹ := by
    have hβi : IsLoUni β⁻¹ := by
      have := loU_inv (show LoU β from hβ); exact this
    have hW' : β⁻¹ * ptMat w * X = ptMat w := by
      have hu := ptMat_isUnit w
      have hβd : IsUnit β.det := by rw [loU_det (show LoU β from hβ)]; exact isUnit_one
      rw [hXdef, show β⁻¹ * ptMat w * ((ptMat w)⁻¹ * β * ptMat w) = β⁻¹ * (ptMat w * (ptMat w)⁻¹) * β * ptMat w by
        simp only [Matrix.mul_assoc], Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.nonsing_inv_mul _ hβd,
        Matrix.one_mul]
    obtain ⟨h1, -, h3⟩ := X_of_st w hβi hX hW'
    have hXi : (ptMat w)⁻¹ * β⁻¹ * ptMat w = X⁻¹ := h1
    rw [← hXi]; exact h3
  rw [hbX]
  constructor
  · intro h a c hac hs
    obtain ⟨h1, h2, h3⟩ := h c a hac
    have hcv : cv w c = cv w a := (pval_eq_blk w a c hs).symm
    have key : ∀ x : D.host.E, cv w a * (x * (cv w a)⁻¹) = x := fun x => by
      rw [mul_comm x, ← mul_assoc, mul_inv_cancel₀ (cv_ne w a), one_mul]
    rw [hβij, hcv, mul_assoc, key] at h1 h3
    exact ⟨h1, h2, h3⟩
  · intro h i j hji
    by_cases hs : blkOf w.1 j.val = blkOf w.1 i.val
    · obtain ⟨h1, h2, h3⟩ := h j i hji hs
      have hcv : cv w i = cv w j := (pval_eq_blk w j i hs).symm
      have key : ∀ x : D.host.E, cv w j * (x * (cv w j)⁻¹) = x := fun x => by
        rw [mul_comm x, ← mul_assoc, mul_inv_cancel₀ (cv_ne w j), one_mul]
      rw [hβij, hcv, mul_assoc, key]
      exact ⟨h1, h2, h3⟩
    · have hs' : blkOf w.1 (pinv w i).val ≠ blkOf w.1 (pinv w j).val := by
        rw [blkOf_pinv, blkOf_pinv]; exact fun e => hs e.symm
      have hb0 : X⁻¹ j i = 0 := hXiB j i hs
      have hbt : bt D X⁻¹ j i = 0 := by simp [bt, hb0]
      rw [hβij, hXB _ _ hs', mul_zero, zero_mul, hbt, map_zero, sub_zero]
      exact ⟨FractionalIdeal.zero_mem _, FractionalIdeal.zero_mem _, FractionalIdeal.zero_mem _⟩

theorem mem_stabInt_iff_X (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word)
    (w : Point D.host.E (D.R.rS + 1)) (β : GLR D) (hβ : IsLoUni (β : MatR D)) {b : MatR D} (hb : IsUpUni b)
    (hW : (β : MatR D) * ptMat w * b = ptMat w) :
    β ∈ stabInt D u u' δ M w ↔ CondX w ((ptMat w)⁻¹ * (β : MatR D) * ptMat w) := by
  rw [stabIntShape D δ M hA u u' w β]
  constructor
  · rintro ⟨-, b', hb', hW', hE⟩
    exact (entryShape_iff w hβ hb' hW').1 hE
  · intro h
    exact ⟨hβ, b, hb, hW, (entryShape_iff w hβ hb hW).2 h⟩

end Formalism.L2.SG.Pf.StabIntSh
