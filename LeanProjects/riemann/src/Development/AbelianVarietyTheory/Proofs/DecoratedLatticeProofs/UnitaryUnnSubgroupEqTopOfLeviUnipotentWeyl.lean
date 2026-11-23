import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHermIsUnitGeneric

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Gen
open GlobalTheory.StdUnn.Model
variable {D : D7} {n : ℕ}

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem exists_blockMatrixTwoByTwoFin_eq {R : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : ∃ a b c d, M = blk4 a b c d := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  rw [blk4, Matrix.fromBlocks_toBlocks]
  ext i j
  simp

theorem rel {g : G D n} {a b c d : Mx D n n} (hg : mat g = blk4 a b c d) :
    -(adj c * a) + adj a * c = 0 ∧ -(adj c * b) + adj a * d = 1 ∧ -(adj d * b) + adj b * d = 0 := by
  have h : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n) := g.2
  rw [JR_Jst, hg] at h
  simp only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, mul_zero, mul_one, add_zero, zero_add, mul_neg, neg_mul] at h
  exact ⟨(blockMatrixTwoByTwoFin_injective h).1, (blockMatrixTwoByTwoFin_injective h).2.1, (blockMatrixTwoByTwoFin_injective h).2.2.2⟩

variable {S : Subgroup (G D n)}
  (hm : ∀ (g : G D n) (a : GL (Fin n) (AE D)), mat g = blk4 a.1 0 0 (adj (a⁻¹).1) → g ∈ S)
  (hn : ∀ (g : G D n) (b : Mx D n n), mat g = blk4 1 b 0 1 → g ∈ S)
  (hw : ∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S)

include hm hn in
theorem mem_of_upper {g : G D n} {a b d : Mx D n n} (hg : mat g = blk4 a b 0 d) (ha : IsUnit a) : g ∈ S := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨m, hmm⟩ := exists_levi (D := D) (n := n) u⁻¹
  have h1 : (adj u.1 : Mx D n n) * d = 1 := by simpa using (rel hg).2.1
  rw [← S.mul_mem_cancel_left (hm m _ hmm)]
  refine hn _ ((u⁻¹).1 * b) ?_
  rw [mat_mul, hmm, hg, submatrix_fromBlocks_mul]
  simp only [inv_inv, Units.inv_mul, mul_zero, zero_mul, add_zero, zero_add, h1]

include hm hn hw in
theorem mem_of_lower {g : G D n} {a c d : Mx D n n} (hg : mat g = blk4 a 0 c d) (hd : IsUnit d) : g ∈ S := by
  obtain ⟨w, hww⟩ := exists_weyl (D := D) (n := n)
  rw [← S.mul_mem_cancel_left (hw w hww), ← S.mul_mem_cancel_right (hw w hww)]
  refine mem_of_upper hm hn (a := -d) (b := c) (d := -a) ?_ hd.neg
  rw [mat_mul, mat_mul, hww, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp

include hm hn hw in
theorem mem_of_isUnit {g : G D n} {a b c d : Mx D n n} (hg : mat g = blk4 a b c d) (hd : IsUnit d) : g ∈ S := by
  obtain ⟨u, rfl⟩ := hd
  have h1 : (adj u.1 : Mx D n n) * b = adj b * u.1 := neg_add_eq_zero.1 (rel hg).2.2
  have h2 : (adj (u⁻¹).1 : Mx D n n) * adj u.1 = 1 := by rw [← adj_mul, Units.mul_inv, adj_one]
  have h3 : (adj (-(b * (u⁻¹).1)) : Mx D n n) = -(b * (u⁻¹).1) := by
    rw [adj_neg, adj_mul]
    congr 1
    calc (adj (u⁻¹).1 : Mx D n n) * adj b = adj (u⁻¹).1 * (adj b * u.1) * (u⁻¹).1 := by
          rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
      _ = b * (u⁻¹).1 := by rw [← h1, ← mul_assoc, h2, one_mul]
  obtain ⟨x, hx⟩ := (exists_unip _).2 h3
  rw [← S.mul_mem_cancel_left (hn x _ hx)]
  refine mem_of_lower hm hn hw (a := a + -(b * (u⁻¹).1) * c) (c := c) (d := u.1) ?_ u.isUnit
  rw [mat_mul, hx, hg, submatrix_fromBlocks_mul]
  simp only [one_mul, zero_mul, zero_add, neg_mul, mul_assoc, Units.inv_mul, mul_one, add_neg_cancel]

end GlobalTheory.StdUnn.Gen

namespace GlobalTheory.StdUnn

theorem eq_top_of_levi_unip_weyl : ∀ (D : D7) (n : ℕ) (S : Subgroup (GlobalTheory.StdUnn.G D n)), (∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 a.1 0 0 (GlobalTheory.MixModel.adj (a⁻¹).1) → g ∈ S) → (∀ (g : GlobalTheory.StdUnn.G D n) (b : Mx D n n), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 1 b 0 1 → g ∈ S) → (∀ g : GlobalTheory.StdUnn.G D n, GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 → g ∈ S) → S = ⊤ := by
  intro D n S hm hn hw
  rw [eq_top_iff]
  intro g _
  obtain ⟨a, b, c, d, hg⟩ := Gen.exists_blockMatrixTwoByTwoFin_eq (mat g)
  obtain ⟨p', p, q', q, hi⟩ := Gen.exists_blockMatrixTwoByTwoFin_eq (mat g⁻¹)
  have h1 : mat g * mat g⁻¹ = 1 := by rw [← Gen.mat_mul, mul_inv_cancel]; rfl
  rw [hg, hi, Model.submatrix_fromBlocks_mul, ← Model.block_matrix_one] at h1
  obtain ⟨x, hx, hu⟩ := GlobalTheory.HermTransversal.exists_herm_isUnit D n c d p q (Model.blockMatrixTwoByTwoFin_injective h1).2.2.2
  obtain ⟨y, hy⟩ := (Model.exists_unip x).2 hx
  rw [← S.mul_mem_cancel_right (hn y _ hy)]
  refine Gen.mem_of_isUnit hm hn hw (a := a) (b := a * x + b) (c := c) (d := c * x + d) ?_ hu
  rw [Gen.mat_mul, hg, hy, Model.submatrix_fromBlocks_mul]
  simp only [mul_one, mul_zero, add_zero]

end GlobalTheory.StdUnn

end
