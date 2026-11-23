import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCovariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantWeylInvolution

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.EisCovar PositivityTheory.GramSchwartzFunctions.EC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTw

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

section Blocks

variable {R : Type} [CommRing R]

theorem block_mul₂ (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one (hn : ρ + p = n) : bl hn (1 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (1 : Matrix (Fin p) (Fin p) R) = 1 := by
  simp only [bl, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrix_zero (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (0 : Matrix (Fin p) (Fin p) R) = 0 := by
  simp only [bl, Matrix.fromBlocks_zero]
  rfl

theorem bl_add (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  simp only [bl]
  rw [← Matrix.fromBlocks_add]
  rfl

theorem blockMatrix_inj (hn : ρ + p = n) {a a' : Matrix (Fin ρ) (Fin ρ) R} {b b' : Matrix (Fin ρ) (Fin p) R}
    {c c' : Matrix (Fin p) (Fin ρ) R} {d d' : Matrix (Fin p) (Fin p) R}
    (h : bl hn a b c d = bl hn a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h2 := congrArg (fun M => M.submatrix (finSumFinEquiv.trans (finCongr hn)) (finSumFinEquiv.trans (finCongr hn))) h
  simp only [bl, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2
  exact Matrix.fromBlocks_inj.1 h2

theorem block_matrix_injective {a a' b b' c c' d d' : Matrix (Fin n) (Fin n) R}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h2 := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
  simp only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2
  exact Matrix.fromBlocks_inj.1 h2

end Blocks

theorem mat_nzx_sh (M : Maps D hn) (z : hermA D ρ) (x y : Mx D ρ p) :
    mat (M.nzx z x * M.sh y) = blk4 (bl hn 1 y 0 1) (bl hn (z.1 - x ⬝ adj y) x (adj x) 0) 0 (bl hn 1 0 (-adj y) 1) := by
  rw [mat_mul', M.nzx_mat, M.sh_mat, submatrix_fromBlocks_mul]
  congr 1
  · simp
  · rw [Matrix.mul_zero, zero_add, block_mul₂]
    simp [sub_eq_add_neg]
  · simp
  · simp

theorem nzx_sh_inj (M : Maps D hn) {z z' : hermA D ρ} {x x' y y' : Mx D ρ p}
    (h : M.nzx z x * M.sh y = M.nzx z' x' * M.sh y') : z = z' ∧ x = x' ∧ y = y' := by
  have h2 := congrArg mat h
  rw [mat_nzx_sh, mat_nzx_sh] at h2
  obtain ⟨h3, h4, -, -⟩ := block_matrix_injective h2
  obtain ⟨-, rfl, -, -⟩ := blockMatrix_inj hn h3
  obtain ⟨h5, rfl, -, -⟩ := blockMatrix_inj hn h4
  exact ⟨Subtype.ext (sub_left_injective h5), rfl, rfl⟩

set_option maxHeartbeats 1000000 in
theorem gl_levi (M : Maps D hn) (g : G D p) (a : GL (Fin p) (AE D)) (hg : mat g = blk4 a.1 0 0 (adj (a⁻¹).1))
    (z : hermA D ρ) (x y : Mx D ρ p) :
    M.emb g * (M.nzx z x * M.sh y) = M.nzx z (x ⬝ adj a.1) * M.sh (y ⬝ (a⁻¹).1) * M.emb g := by
  have h1 : (a⁻¹).1 * a.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : adj a.1 * adj (a⁻¹).1 = 1 := by
    have := adj_mul (a⁻¹).1 a.1
    rw [show HMul.hMul (a⁻¹).1 a.1 = (1 : Mx D p p) from h1, adj_one] at this
    exact this.symm
  have hE := M.emb_mat g _ _ _ _ hg
  apply mat_injective'
  rw [mat_mul' (M.emb g), mat_mul' _ (M.emb g), mat_nzx_sh, mat_nzx_sh, hE, blockMatrix_zero, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  have h3 : ∀ w : Mx D p ρ, adj a.1 ⬝ (adj (a⁻¹).1 ⬝ w) = w := fun w => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have h4 : ∀ w : Mx D ρ p, w ⬝ adj a.1 ⬝ adj (a⁻¹).1 = w := fun w => by
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  have h5 : ∀ w : Mx D ρ p, w ⬝ (a⁻¹).1 ⬝ a.1 = w := fun w => by
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, block_mul₂, adj_mul, adj_adj, Matrix.one_mul,
    Matrix.mul_one, h4, h5, Matrix.mul_assoc x, h3, Matrix.mul_neg, Matrix.neg_mul, neg_zero]

theorem adj_sub' {k l : ℕ} (u v : Mx D k l) : adj (u - v) = adj u - adj v := by
  rw [sub_eq_add_neg, adj_add, adj_neg, sub_eq_add_neg]

def zU (z : hermA D ρ) (y : Mx D ρ p) (b : Mx D p p) (hb : adj b = b) : hermA D ρ :=
  ⟨z.1 - y ⬝ (b ⬝ adj y), by
    show adj _ = _
    rw [adj_sub', adj_mul, adj_mul, adj_adj, hb, z.2, Matrix.mul_assoc]⟩

set_option maxHeartbeats 1000000 in
theorem gl_unip (M : Maps D hn) (g : G D p) (b : Mx D p p) (hb : adj b = b) (hg : mat g = blk4 1 b 0 1)
    (z : hermA D ρ) (x y : Mx D ρ p) :
    M.emb g * (M.nzx z x * M.sh y) = M.nzx (zU z y b hb) (x - y ⬝ b) * M.sh y * M.emb g := by
  have hE := M.emb_mat g _ _ _ _ hg
  apply mat_injective'
  rw [mat_mul' (M.emb g), mat_mul' _ (M.emb g), mat_nzx_sh, mat_nzx_sh, hE, blockMatrix_zero, blockRowSubstitution_one, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, block_mul₂, bl_add, adj_sub', adj_mul, hb]
  have e1 : (zU z y b hb).1 - (x - y ⬝ b) ⬝ adj y = z.1 - x ⬝ adj y := by
    simp only [zU, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  have e2 : y ⬝ b + (x - y ⬝ b) = x := by abel
  have e3 : adj x + b ⬝ -adj y = adj x - b ⬝ adj y := by rw [Matrix.mul_neg, sub_eq_add_neg]
  rw [e1, e2, e3]

def zW (z : hermA D ρ) (x y : Mx D ρ p) : hermA D ρ :=
  ⟨z.1 - x ⬝ adj y - y ⬝ adj x, by
    show adj _ = _
    rw [adj_sub', adj_sub', adj_mul, adj_mul, adj_adj, adj_adj, z.2]
    abel⟩

set_option maxHeartbeats 1000000 in
theorem gl_weyl (M : Maps D hn) (g : G D p) (hg : mat g = blk4 0 1 (-1) 0)
    (z : hermA D ρ) (x y : Mx D ρ p) :
    M.emb g * (M.nzx z x * M.sh y) = M.nzx (zW z x y) (-y) * M.sh x * M.emb g := by
  have hE := M.emb_mat g _ _ _ _ hg
  apply mat_injective'
  rw [mat_mul' (M.emb g), mat_mul' _ (M.emb g), mat_nzx_sh, mat_nzx_sh, hE, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  have e1 : (zW z x y).1 - -y ⬝ adj x = z.1 - x ⬝ adj y := by
    simp only [zW, Matrix.neg_mul]
    abel
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, block_mul₂, bl_add, adj_neg, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg, neg_zero]
  rw [show (zW z x y).1 - -(y ⬝ adj x) = z.1 - x ⬝ adj y by rw [← Matrix.neg_mul]; exact e1]

end GlobalTheory.CompanionTheory.ThTw
