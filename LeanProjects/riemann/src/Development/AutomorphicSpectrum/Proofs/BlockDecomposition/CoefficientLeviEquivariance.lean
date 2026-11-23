import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WzLevi

open GlobalTheory.StdUnn.Model (submatrix_fromBlocks_mul block_matrix_one)
open GlobalTheory.CompanionTheory.PcB (blockMatrix_multiply blockMatrix_add' blockMatrix_one mat_mul')
open GlobalTheory.CompanionTheory.IwaAd (levi_mem_P adj_mul_adj_inv adj_inv_mul_adj)

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem adj_zero' {k l : ℕ} : adj (0 : Mx D k l) = 0 := by
  have h := adj_add (0 : Mx D k l) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem blkA_blk4 {R : Type} {k : ℕ} (a b c d : Matrix (Fin k) (Fin k) R) : blkA (blk4 a b c d) = a := by
  simp only [blkA, blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id,
    Matrix.toBlocks_fromBlocks₁₁]

theorem blockMatrix_zero' {R : Type} [CommRing R] (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (0 : Matrix (Fin p) (Fin p) R) = 0 := by
  simp only [bl, Matrix.fromBlocks_zero]
  rfl

theorem emb_comm (M : Maps D hn) (ζ : hermA D ρ) (g₀ : G D p) (a : GL (Fin p) (AE D))
    (hg : mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1)) :
    M.w * M.nzx ζ 0 * M.emb g₀ = M.emb g₀ * (M.w * M.nzx ζ 0) := by
  have hE := M.emb_mat g₀ _ _ _ _ hg
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  simp only [mat_mul']
  rw [hE, M.w_mat, M.nzx_mat, adj_zero']
  simp only [submatrix_fromBlocks_mul]
  simp only [blockMatrix_zero' hn, blockMatrix_add', blockMatrix_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, neg_zero]

theorem mat_inv_levi (g₀ : G D p) (a : GL (Fin p) (AE D)) (hg : mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1)) :
    mat g₀⁻¹ = blk4 (a⁻¹).1 0 0 (adj a.1) := by
  have h1 : HMul.hMul (mat g₀) (blk4 (a⁻¹).1 0 0 (adj a.1)) = (1 : Mx D (p + p) (p + p)) := by
    rw [hg, submatrix_fromBlocks_mul]
    have e1 : a.1 * (a⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e2 : HMul.hMul (adj (a⁻¹).1) (adj a.1) = (1 : Mx D p p) := adj_inv_mul_adj a
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e1, e2]
    exact block_matrix_one
  calc mat g₀⁻¹ = HMul.hMul (mat g₀⁻¹) (HMul.hMul (mat g₀) (blk4 (a⁻¹).1 0 0 (adj a.1))) := by
        rw [h1]; exact (Matrix.mul_one _).symm
    _ = HMul.hMul (mat (g₀⁻¹ * g₀)) (blk4 (a⁻¹).1 0 0 (adj a.1)) := by
        rw [mat_mul']; exact (Matrix.mul_assoc _ _ _).symm
    _ = blk4 (a⁻¹).1 0 0 (adj a.1) := by
        rw [inv_mul_cancel]; exact Matrix.one_mul _

theorem exists_lv (hn : ρ + p = n) (a : GL (Fin p) (AE D)) :
    ∃ b : GL (Fin n) (AE D), b.1 = bl hn 1 0 0 a.1 := by
  have e : a.1 * (a⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e' : (a⁻¹).1 * a.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨⟨bl hn 1 0 0 a.1, bl hn 1 0 0 (a⁻¹).1, ?_, ?_⟩, rfl⟩
  · rw [blockMatrix_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, e]
    exact blockMatrix_one hn
  · rw [blockMatrix_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, e']
    exact blockMatrix_one hn

theorem det_lv (hn : ρ + p = n) (a : GL (Fin p) (AE D)) (b : GL (Fin n) (AE D)) (hb : b.1 = bl hn 1 0 0 a.1) :
    Matrix.GeneralLinearGroup.det b = Matrix.GeneralLinearGroup.det a := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hb]
  simp only [bl]
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

theorem wz_emb : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ)
  (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ), IsLaw χ z f → ∀ (g₀ : G D p) (a : GL (Fin p) (AE D)),
  mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1) → ∀ x : G D n, Wz M m ψ b₀ f (M.emb g₀ * x) =
    (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) * Wz M m ψ b₀ f x := by
  intro D n ρ p hn M m ψ b₀ χ z f hf g₀ a hg x
  have hE := M.emb_mat g₀ _ _ _ _ hg
  have hE' := M.emb_mat g₀⁻¹ _ _ _ _ (mat_inv_levi g₀ a hg)
  rw [blockMatrix_zero' hn] at hE hE'
  have hP : M.emb g₀ ∈ P D n :=
    levi_mem_P hE hE' (by rw [← map_mul, inv_mul_cancel, map_one])
  obtain ⟨b, hb⟩ := exists_lv hn a
  have hA : blkA (mat (M.emb g₀)) = b.1 := by
    rw [hE, blkA_blk4, hb]
  have e : ∀ ζ : hermA D ρ, f (M.w * M.nzx ζ 0 * (M.emb g₀ * x)) =
      (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) *
        f (M.w * M.nzx ζ 0 * x) := by
    intro ζ
    rw [← mul_assoc, emb_comm M ζ g₀ a hg, mul_assoc, hf _ hP b hA, det_lv hn a b hb]
  simp only [Wz]
  simp only [e]
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul]

end GlobalTheory.CompanionTheory.WzLevi

end
