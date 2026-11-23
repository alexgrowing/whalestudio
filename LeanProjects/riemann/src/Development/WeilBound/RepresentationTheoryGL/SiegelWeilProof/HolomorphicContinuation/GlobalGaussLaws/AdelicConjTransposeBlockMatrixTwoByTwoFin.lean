import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellA

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LeviH

variable {D : D7}

def bA {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁

def bB {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂

def bC {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁

def bD {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

theorem block_matrix_of_blocks {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    M = blk4 (bA M) (bB M) (bC M) (bD M) := by
  unfold blk4 bA bB bC bD
  rw [Matrix.fromBlocks_toBlocks, Matrix.submatrix_submatrix]
  simp

theorem upper_left_of_block_matrix {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : bA (blk4 a b c d) = a := by
  unfold bA blk4
  rw [Matrix.submatrix_submatrix]
  simp

theorem upper_right_of_block_matrix {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : bB (blk4 a b c d) = b := by
  unfold bB blk4
  rw [Matrix.submatrix_submatrix]
  simp

theorem bA_reidx {n : ℕ} (y : M2 n) : bA (reidx y) = y.toBlocks₁₁ := by
  unfold bA reidx
  rw [Matrix.submatrix_submatrix]
  simp

theorem bB_reidx {n : ℕ} (y : M2 n) : bB (reidx y) = y.toBlocks₁₂ := by
  unfold bB reidx
  rw [Matrix.submatrix_submatrix]
  simp

theorem bC_reidx {n : ℕ} (y : M2 n) : bC (reidx y) = y.toBlocks₂₁ := by
  unfold bC reidx
  rw [Matrix.submatrix_submatrix]
  simp

theorem bB_one {R : Type} [CommRing R] {n : ℕ} : bB (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 0 := by
  rw [← GlobalTheory.StdUnn.Frame.block_matrix_one, upper_right_of_block_matrix]

theorem bA_one {R : Type} [CommRing R] {n : ℕ} : bA (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  rw [← GlobalTheory.StdUnn.Frame.block_matrix_one, upper_left_of_block_matrix]

theorem lower_left_of_block_matrix {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : bC (blk4 a b c d) = c := by
  unfold bC blk4
  rw [Matrix.submatrix_submatrix]
  simp

theorem bC_one {R : Type} [CommRing R] {n : ℕ} : bC (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 0 := by
  rw [← GlobalTheory.StdUnn.Frame.block_matrix_one, lower_left_of_block_matrix]

theorem bA_map {R S : Type} {n : ℕ} (f : R → S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (bA M).map f = bA (M.map f) := rfl

theorem bB_map {R S : Type} {n : ℕ} (f : R → S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (bB M).map f = bB (M.map f) := rfl

theorem bC_map {R S : Type} {n : ℕ} (f : R → S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (bC M).map f = bC (M.map f) := rfl

theorem compAt_bA (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (M : Mx D (n + n) (n + n)) :
    compAt θ τ (bA M) = bA (compAt θ τ M) := rfl

theorem compAt_bB (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (M : Mx D (n + n) (n + n)) :
    compAt θ τ (bB M) = bB (compAt θ τ M) := rfl

theorem compAt_bC (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (M : Mx D (n + n) (n + n)) :
    compAt θ τ (bC M) = bC (compAt θ τ M) := rfl

theorem adj_mul {m n k : ℕ} (x : Mx D m n) (z : Mx D n k) :
    adj (HMul.hMul x z : Mx D m k) = HMul.hMul (adj z) (adj x) := by
  unfold adj
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem adj_one {n : ℕ} : adj (1 : Mx D n n) = 1 := by
  unfold adj
  rw [Matrix.map_one _ (map_zero (cA D)) (map_one (cA D)), Matrix.transpose_one]

theorem adelicConjTranspose_blockMatrixTwoByTwoFin {n : ℕ} (a d : Mx D n n) : adj (blk4 a 0 0 d) = blk4 (adj a) 0 0 (adj d) := by
  unfold adj
  rw [GlobalTheory.StdUnn.Frame.block_matrix_map, GlobalTheory.StdUnn.Frame.blockMatrixTwoByTwoFin_transpose, Matrix.map_zero _ (map_zero (cA D)),
    Matrix.transpose_zero]

theorem unitary_mat {n : ℕ} (g : G D n) :
    adj (mat g) * (blk4 0 1 (-1) 0 : Mx D (n + n) (n + n)) * mat g = blk4 0 1 (-1) 0 := by
  have h : adj (mat g) * rat (Jst D n) * mat g = rat (Jst D n) := g.2
  rwa [GlobalTheory.StdUnn.Frame.rat_Jst] at h

end PositivityTheory.Rg.Sw.Glob.LeviH

namespace PositivityTheory.Rg.Sw.Glob

open LeviH in
set_option maxHeartbeats 800000 in
theorem leviTau : LeviTau := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y a ha hya
  have hθ := hC.hθ
  obtain ⟨hτ, hτ', hfin⟩ := hC.hι.2 y
  have h1 : mat (ι y) * mat (ι y)⁻¹ = 1 := by
    show mat (ι y * (ι y)⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  have h2 : mat (ι y)⁻¹ * mat (ι y) = 1 := by
    show mat ((ι y)⁻¹ * ι y) = 1
    rw [inv_mul_cancel]
    rfl
  have hU := unitary_mat (ι y)
  have hlevi := hC.hω.levi (ι y)
  generalize mat (ι y) = M at hτ hτ' hfin h1 h2 hU hlevi
  generalize mat (ι y)⁻¹ = M' at h1 h2
  have hB : bB M = 0 := by
    apply GlobalTheory.StabAtPlace.mx_ext hθ
    · rw [Matrix.map_zero _ (map_zero (finPart D)), bB_map, hfin, bB_one]
    · intro τ'
      rw [OG.compAt_zero', compAt_bB]
      by_cases h : τ' = τ
      · subst h
        rw [hτ, bB_reidx, hya]
        simp only [mM, Matrix.toBlocks_fromBlocks₁₂]
      · rw [hτ' τ' h, bB_one]
  have hC0 : bC M = 0 := by
    apply GlobalTheory.StabAtPlace.mx_ext hθ
    · rw [Matrix.map_zero _ (map_zero (finPart D)), bC_map, hfin, bC_one]
    · intro τ'
      rw [OG.compAt_zero', compAt_bC]
      by_cases h : τ' = τ
      · subst h
        rw [hτ, bC_reidx, hya]
        simp only [mM, Matrix.toBlocks_fromBlocks₂₁]
      · rw [hτ' τ' h, bC_one]
  have hM : M = blk4 (bA M) 0 0 (bD M) := by
    conv_lhs => rw [block_matrix_of_blocks M]
    rw [hB, hC0]
  have hAA' : bA M * bA M' = 1 := by
    have e := congrArg bA h1
    rw [hM, block_matrix_of_blocks M', GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, upper_left_of_block_matrix, bA_one, zero_mul, add_zero] at e
    exact e
  have hA'A : bA M' * bA M = 1 := by
    have e := congrArg bA h2
    rw [hM, block_matrix_of_blocks M', GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, upper_left_of_block_matrix, bA_one, mul_zero, add_zero] at e
    exact e
  have hAD : adj (bA M) * bD M = 1 := by
    rw [hM, adelicConjTranspose_blockMatrixTwoByTwoFin, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul] at hU
    have e := congrArg bB hU
    rw [upper_right_of_block_matrix, upper_right_of_block_matrix] at e
    simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one] at e
    exact e
  have hD : bD M = adj (bA M') := by
    have e : adj (bA M') * adj (bA M) = 1 := by rw [← LeviH.adj_mul, hAA', LeviH.adj_one]
    calc bD M = 1 * bD M := (one_mul _).symm
      _ = adj (bA M') * (adj (bA M) * bD M) := by rw [← mul_assoc, e]
      _ = adj (bA M') := by rw [hAD, mul_one]
  have hmat : M = blk4 (bA M) 0 0 (adj (bA M')) := by
    calc M = blk4 (bA M) 0 0 (bD M) := hM
      _ = blk4 (bA M) 0 0 (adj (bA M')) := by rw [hD]
  refine ⟨_, bA M, ?_, ?_, ?_, fun Φ x => hlevi ⟨bA M, bA M', hAA', hA'A⟩ hmat Φ x⟩
  · rw [compAt_bA, hτ, bA_reidx, hya]
    simp only [mM, Matrix.toBlocks_fromBlocks₁₁]
  · intro τ' h
    rw [compAt_bA, hτ' τ' h, bA_one]
  · rw [bA_map, hfin, bA_one]

end PositivityTheory.Rg.Sw.Glob
