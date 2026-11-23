import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GlobalGaussBlockRelations

variable {D : D7} {n : ℕ}

def bA (M : Mx D (n + n) (n + n)) : Mx D n n := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁

def bB (M : Mx D (n + n) (n + n)) : Mx D n n := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂

def bC (M : Mx D (n + n) (n + n)) : Mx D n n := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁

theorem siegelParabolicUnn_matrix_blockUpperTriangular (M : Mx D (n + n) (n + n)) : M = blk4 (bA M) (bB M) (bC M) (blkDm M) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;> rfl

theorem rel1 (g : G D n) : adj (mat g) * blk4 0 1 (-1) 0 * mat g = blk4 0 1 (-1) 0 := by
  have h : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n) := g.2
  rwa [JR_Jst] at h

theorem JJ_sq : (blk4 0 1 (-1) 0 : Mx D (n + n) (n + n)) * blk4 0 1 (-1) 0 = -1 := by
  rw [submatrix_fromBlocks_mul]
  simp only [mul_one, zero_add, add_zero, mul_neg, mul_zero, neg_zero]
  rw [← block_matrix_one (R := AE D) (n := n)]
  unfold blk4
  rw [show Matrix.fromBlocks (-1 : Mx D n n) 0 0 (-1) = -Matrix.fromBlocks 1 0 0 1 by
    rw [Matrix.fromBlocks_neg]; simp, Matrix.submatrix_neg]
  rfl

set_option maxHeartbeats 1000000 in
theorem rel2 (g : G D n) : mat g * blk4 0 1 (-1) 0 * adj (mat g) = blk4 0 1 (-1) 0 := by
  have hMN : mat g * mat g⁻¹ = 1 := by
    rw [show mat g * mat g⁻¹ = mat (g * g⁻¹) from rfl, mul_inv_cancel]; rfl
  have h1 := rel1 g
  have hJ : (blk4 0 1 (-1) 0 : Mx D (n + n) (n + n)) * blk4 0 1 (-1) 0 = -1 := JJ_sq
  generalize (blk4 0 1 (-1) 0 : Mx D (n + n) (n + n)) = J at h1 hJ ⊢
  generalize mat g⁻¹ = N at hMN
  generalize mat g = M at hMN h1 ⊢
  have h2 : adj M * J = J * N := by
    calc adj M * J = adj M * J * (M * N) := by rw [hMN, mul_one]
      _ = (adj M * J * M) * N := by simp only [mul_assoc]
      _ = J * N := by rw [h1]
  have h3 : N = -(J * adj M * J) := by
    have : J * (adj M * J) = J * (J * N) := by rw [h2]
    rw [← mul_assoc, ← mul_assoc, hJ] at this
    rw [this, neg_mul, one_mul, neg_neg]
  have h4 : M * (J * adj M * J) = -1 := by
    have : M * N = 1 := hMN
    rw [h3, mul_neg] at this
    rw [← neg_neg (M * (J * adj M * J)), this]
  have h5 : M * J * adj M * J = -1 := by rw [← h4]; simp only [mul_assoc]
  calc M * J * adj M = -(M * J * adj M * (J * J)) := by rw [hJ, mul_neg, mul_one, neg_neg]
    _ = -((M * J * adj M * J) * J) := by rw [mul_assoc (M * J * adj M) J J]
    _ = J := by rw [h5, neg_mul, one_mul, neg_neg]

set_option maxHeartbeats 1000000 in
theorem blockRels (g : G D n) :
    adj (bB (mat g)) * blkDm (mat g) = adj (blkDm (mat g)) * bB (mat g) ∧
    adj (bA (mat g)) * blkDm (mat g) - adj (bC (mat g)) * bB (mat g) = 1 ∧
    blkDm (mat g) * adj (bC (mat g)) = bC (mat g) * adj (blkDm (mat g)) ∧
    bA (mat g) * adj (blkDm (mat g)) - bB (mat g) * adj (bC (mat g)) = 1 := by
  have h1 := rel1 g
  have h2 := rel2 g
  rw [siegelParabolicUnn_matrix_blockUpperTriangular (mat g)] at h1 h2
  generalize bA (mat g) = A at h1 h2 ⊢
  generalize bB (mat g) = B at h1 h2 ⊢
  generalize bC (mat g) = C at h1 h2 ⊢
  generalize blkDm (mat g) = Dd at h1 h2 ⊢
  rw [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h1 h2
  simp only [mul_zero, mul_one, add_zero, zero_add, mul_neg, neg_mul] at h1 h2
  obtain ⟨-, e12, -, e22⟩ := blockMatrixTwoByTwoFin_injective h1
  obtain ⟨-, f12, -, f22⟩ := blockMatrixTwoByTwoFin_injective h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (neg_add_eq_zero.1 e22).symm
  · rw [← e12]; abel
  · exact neg_add_eq_zero.1 f22
  · rw [← f12]; abel

end PositivityTheory.Rg.Sw.Glob.GlobalGaussBlockRelations

namespace PositivityTheory.Rg.Sw.Glob

open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.MixModel

set_option maxHeartbeats 2000000 in
theorem unitD : UnitD := by
  intro D n g hD
  obtain ⟨r1, r2, r3, r4⟩ := GlobalGaussBlockRelations.blockRels g
  have hM := GlobalGaussBlockRelations.siegelParabolicUnn_matrix_blockUpperTriangular (mat g)
  generalize GlobalGaussBlockRelations.bA (mat g) = A at r1 r2 r3 r4 hM
  generalize GlobalGaussBlockRelations.bB (mat g) = B at r1 r2 r3 r4 hM
  generalize GlobalGaussBlockRelations.bC (mat g) = C at r1 r2 r3 r4 hM
  generalize blkDm (mat g) = Dd at r1 r2 r3 r4 hM hD
  obtain ⟨Di, hDi1, hDi2⟩ : ∃ Di : Mx D n n, Dd * Di = 1 ∧ Di * Dd = 1 :=
    ⟨Dd⁻¹, Matrix.mul_nonsing_inv Dd hD, Matrix.nonsing_inv_mul Dd hD⟩
  have hA1 : adj Di * adj Dd = 1 := by rw [← adj_mul, hDi1, adj_one]
  have hA2 : adj Dd * adj Di = 1 := by rw [← adj_mul, hDi2, adj_one]
  have hb : adj (B * Di) = B * Di := by
    rw [adj_mul]
    calc adj Di * adj B = adj Di * (adj B * Dd) * Di := by simp only [mul_assoc, hDi1, mul_one]
      _ = adj Di * (adj Dd * B) * Di := by rw [r1]
      _ = B * Di := by rw [← mul_assoc (adj Di), hA1, one_mul]
  have hc : adj (Di * C) = Di * C := by
    rw [adj_mul]
    calc adj C * adj Di = Di * (Dd * adj C) * adj Di := by simp only [← mul_assoc, hDi2, one_mul]
      _ = Di * (C * adj Dd) * adj Di := by rw [r3]
      _ = Di * C := by simp only [mul_assoc, hA2, mul_one]
  have ha1 : (A - B * Di * C) * adj Dd = 1 := by
    rw [sub_mul, mul_assoc (B * Di) C (adj Dd), ← r3, ← mul_assoc (B * Di) Dd (adj C), mul_assoc B Di Dd, hDi2,
      mul_one, r4]
  have ha2 : adj Dd * (A - B * Di * C) = 1 := mul_eq_one_comm.mp ha1
  let aG : GL (Fin n) (AE D) := ⟨A - B * Di * C, adj Dd, ha1, ha2⟩
  obtain ⟨m, hm⟩ := exists_levi aG
  have hm' : mat m = blk4 (A - B * Di * C) 0 0 Dd := by
    rw [hm]
    show blk4 (A - B * Di * C) 0 0 (adj (adj Dd)) = _
    rw [adj_adj]
  obtain ⟨u, hu⟩ := (exists_unip (B * Di)).2 hb
  obtain ⟨v, hv⟩ : ∃ v : G D n, mat v = blk4 1 0 (Di * C) 1 := by
    refine exists_mat _ (blk4 1 0 (-(Di * C)) 1) ?_ ?_ ?_
    · rw [submatrix_fromBlocks_mul]
      simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add, add_neg_cancel]
      exact block_matrix_one
    · rw [submatrix_fromBlocks_mul]
      simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add, neg_add_cancel]
      exact block_matrix_one
    · rw [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, hc]
      simp only [adj_one, adj_zero, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add,
        Matrix.mul_neg, neg_add_cancel]
  have hg : g = u * m * v := by
    apply Subtype.ext
    apply Units.ext
    show mat g = mat u * mat m * mat v
    rw [hM, hu, hm', hv, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    simp only [one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add]
    have e1 : B * Di * Dd = B := by rw [mul_assoc, hDi2, mul_one]
    have e2 : Dd * (Di * C) = C := by rw [← mul_assoc, hDi1, one_mul]
    rw [e1, e2, mul_assoc B Di C, sub_add_cancel]
  rw [hg]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨_, hu⟩))
    (Subgroup.subset_closure (Or.inr (Or.inl ⟨_, _, hm'⟩)))) (Subgroup.subset_closure (Or.inr (Or.inr ⟨_, hv⟩)))

end PositivityTheory.Rg.Sw.Glob
