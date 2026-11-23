import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn.Model

namespace GlobalTheory.CompanionTheory.PcB

open GlobalTheory.CompanionTheory.FourierN (mat_injective)

theorem blockMatrix_zero' {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 0 = 0 := by
  simp only [bl]
  rw [Matrix.fromBlocks_zero]
  rfl

theorem lowerUnipotent_mul_blockDiagonal {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (c : Matrix (Fin p) (Fin ρ) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 0 c 1) (bl hn 1 0 0 d) = bl hn 1 0 c d := by
  rw [blockMatrix_multiply]
  congr 1 <;> simp

theorem blockMatrix_diagonal_mul_lowerUnipotent {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (c : Matrix (Fin p) (Fin ρ) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 0 0 d) (bl hn 1 0 c 1) = bl hn 1 0 (HMul.hMul d c) d := by
  rw [blockMatrix_multiply]
  congr 1 <;> simp

theorem upperUnipotent_mul_blockDiagonal {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (y : Matrix (Fin ρ) (Fin p) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 y 0 1) (bl hn 1 0 0 d) = bl hn 1 (HMul.hMul y d) 0 d := by
  rw [blockMatrix_multiply]
  congr 1 <;> simp

theorem blockMatrix_diagonal_mul_upperUnipotent {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (y : Matrix (Fin ρ) (Fin p) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 0 0 d) (bl hn 1 y 0 1) = bl hn 1 y 0 d := by
  rw [blockMatrix_multiply]
  congr 1 <;> simp

theorem sh_emb_levi (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₀ : G D p)
    (a : GL (Fin p) (AE D)) (h : mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1)) (y : Mx D ρ p) :
    M.sh y * M.emb g₀ = M.emb g₀ * M.sh (HMul.hMul y a.1 : Mx D ρ p) := by
  have hinv : HMul.hMul (adj (a⁻¹).1 : Mx D p p) (adj a.1 : Mx D p p) = (1 : Mx D p p) := by
    have h1 : HMul.hMul (a.1 : Mx D p p) ((a⁻¹).1 : Mx D p p) = (1 : Mx D p p) := by
      exact congrArg Units.val (mul_inv_cancel a)
    rw [← adj_mul, h1]
    exact adj_one
  apply mat_injective
  rw [mat_mul', mat_mul', M.sh_mat, M.sh_mat, M.emb_mat g₀ _ _ _ _ h, blockMatrix_zero', block_diagonal_mul, block_diagonal_mul]
  congr 1
  · rw [upperUnipotent_mul_blockDiagonal, blockMatrix_diagonal_mul_upperUnipotent]
  · have hk : HMul.hMul (adj (a⁻¹).1 : Mx D p p) (adj (HMul.hMul y a.1 : Mx D ρ p)) = adj y := by
      rw [adj_mul, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    have hk' : HMul.hMul (adj (a⁻¹).1 : Mx D p p) (-adj (HMul.hMul y a.1 : Mx D ρ p)) = -adj y := by
      rw [Matrix.mul_neg, hk]
    rw [lowerUnipotent_mul_blockDiagonal, blockMatrix_diagonal_mul_lowerUnipotent, hk']

end GlobalTheory.CompanionTheory.PcB
