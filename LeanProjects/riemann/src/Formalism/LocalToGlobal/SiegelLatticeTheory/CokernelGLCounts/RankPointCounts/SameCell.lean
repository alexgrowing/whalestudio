import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupMUIndep

noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

section Sg

variable {K : Type*} [Field K] {r : ℕ}

def Sg (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K := Matrix.diagonal fun b => (-1) ^ (r - b.val)

theorem Sg_mul_Sg : (Sg r : Matrix (Fin (r + 1)) (Fin (r + 1)) K) * Sg r = 1 := by
  rw [Sg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem zhatOM_eq (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ZhatOM Z = Z * Sg r := by
  ext a b
  rw [Sg, Matrix.mul_diagonal]
  show (-1) ^ (r - b.val) * Z a b = _
  ring

theorem upUni_Sg {U : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni U) : IsUpUni (Sg r * U * Sg r) := by
  intro i j
  simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun hji => by rw [(h i j).1 hji]; ring, fun hij => ?_⟩
  subst hij
  rw [(h i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]
  simp

end Sg

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem same_cell (F : FlagG S r T) (F1 F2 : FlagG S r T') (hG1 : Gflag F F1 ≠ 0) (hG2 : Gflag F F2 ≠ 0)
    (w : Point E (r + 1)) (h1 : IsInCell (ZhatOM (Zhat F F1)) w) (h2 : IsInCell (ZhatOM (Zhat F F2)) w) :
    ∃ g : S.V ≃ₗ[E] S.V, g ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧
      (∃ M : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni M ∧ ∀ b, g.symm (F.fvec b) = ∑ c, M c b • F.fvec c) ∧
      ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni U ∧ ∀ b, g (∑ c, U c b • F1.fvec c) = F2.fvec b := by
  obtain ⟨L1, U1, hL1, hU1, e1⟩ := h1
  obtain ⟨L2, U2, hL2, hU2, e2⟩ := h2
  rw [zhatOM_eq] at e1 e2
  have hL1d : IsUnit L1.det := by rw [loUni_det hL1]; exact isUnit_one
  have hU1d : IsUnit U1.det := by rw [upUni_det hU1]; exact isUnit_one
  set L := L2 * L1⁻¹ with hL
  set U := Sg r * (U1⁻¹ * U2) * Sg r with hU
  have hLl : IsLoUni L := loUni_mul hL2 (loUni_inv hL1)
  have hUu : IsUpUni U := upUni_Sg (upUni_mul (upUni_inv hU1) hU2)
  have hZ : Zhat F F2 = L * Zhat F F1 * U := by
    have z1 : Zhat F F1 = L1 * ptMat w * U1 * Sg r := by
      rw [← e1, Matrix.mul_assoc, Sg_mul_Sg, Matrix.mul_one]
    have z2 : Zhat F F2 = L2 * ptMat w * U2 * Sg r := by
      rw [← e2, Matrix.mul_assoc, Sg_mul_Sg, Matrix.mul_one]
    rw [z2, z1, hL, hU]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Sg r) (Sg r), Sg_mul_Sg, Matrix.one_mul, ← Matrix.mul_assoc U1 U1⁻¹,
      Matrix.mul_nonsing_inv _ hU1d, Matrix.one_mul, ← Matrix.mul_assoc L1⁻¹ L1,
      Matrix.nonsing_inv_mul _ hL1d, Matrix.one_mul]
  set M := Lᴴ with hM
  have hMu : IsUpUni M := loUni_iff_ct.1 hLl
  have hZ' : Zhat F F2 = Mᴴ * Zhat F F1 * U := by rw [hM, conjTranspose_conjTranspose]; exact hZ
  obtain ⟨g, hg, hgx⟩ := witt_tuple (tupMU F F1 M U) (Sum.elim F.fvec F2.fvec) (tupMU_indep F F1 M U hMu hUu hG1)
    (PI.PairCorankPos.W.linIndep F F2 hG2) (gram_moved F F1 F2 M U hMu hUu hZ')
  refine ⟨g, hg, ⟨M, hMu, fun b => ?_⟩, U, hUu, fun b => hgx (Sum.inr b)⟩
  have := hgx (Sum.inl b)
  simp only [tupMU, Sum.elim_inl] at this
  rw [← this, LinearEquiv.symm_apply_apply]

end Formalism.L2.SG.NGCut.NormalVectorPairings
