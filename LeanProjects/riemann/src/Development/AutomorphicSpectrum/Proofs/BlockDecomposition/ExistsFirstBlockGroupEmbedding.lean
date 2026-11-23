import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FirstBlockEmb

open GlobalTheory.StdUnn.Model
open GlobalTheory.CompanionTheory.JacobiMaps (b11 b12 b21 b22 block_matrix_of_blocks upperLeft_block upperRight_block lowerLeft_block_entry lowerRight_block continuous_block_matrix continuous_bl
  block_mul₂ bl_add block_sub blockRowSubstitution_one blockMatrix_zero blockMatrix_neg_one adj_bl adjoint_symplectic_block_product mkG isU_mat)

variable {D : D7} {n ρ p : ℕ}

def firstM (hn : ρ + p = n) (M : Mx D (ρ + ρ) (ρ + ρ)) : Mx D (n + n) (n + n) :=
  blk4 (bl hn (b11 M) 0 0 1) (bl hn (b12 M) 0 0 0) (bl hn (b21 M) 0 0 0) (bl hn (b22 M) 0 0 1)

theorem first_block_embedding_block (hn : ρ + p = n) (a b c d : Mx D ρ ρ) :
    firstM hn (blk4 a b c d) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1) := by
  rw [firstM, upperLeft_block, upperRight_block, lowerLeft_block_entry, lowerRight_block]

def firstMon (hn : ρ + p = n) : Mx D (ρ + ρ) (ρ + ρ) →* Mx D (n + n) (n + n) where
  toFun := firstM hn
  map_one' := by
    rw [← block_matrix_one (R := AE D) (n := ρ), first_block_embedding_block, blockRowSubstitution_one]
    have e : bl hn (0 : Mx D ρ ρ) 0 0 (0 : Mx D p p) = 0 := blockMatrix_zero hn
    rw [e, block_matrix_one]
  map_mul' M N := by
    rw [← block_matrix_of_blocks M, ← block_matrix_of_blocks N]
    generalize b11 M = a
    generalize b12 M = b
    generalize b21 M = c
    generalize b22 M = d
    generalize b11 N = a'
    generalize b12 N = b'
    generalize b21 N = c'
    generalize b22 N = d'
    rw [submatrix_fromBlocks_mul, first_block_embedding_block, first_block_embedding_block, first_block_embedding_block, submatrix_fromBlocks_mul]
    simp only [block_mul₂, bl_add, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]

theorem firstM_isU (hn : ρ + p = n) (M : Mx D (ρ + ρ) (ρ + ρ))
    (h : (adj M * blk4 0 1 (-1) 0 * M : Mx D (ρ + ρ) (ρ + ρ)) = blk4 0 1 (-1) 0) :
    (adj (firstM hn M) * blk4 0 1 (-1) 0 * firstM hn M : Mx D (n + n) (n + n)) = blk4 0 1 (-1) 0 := by
  rw [← block_matrix_of_blocks M] at h ⊢
  generalize b11 M = a at h ⊢
  generalize b12 M = b at h ⊢
  generalize b21 M = c at h ⊢
  generalize b22 M = d at h ⊢
  rw [adjoint_symplectic_block_product] at h
  obtain ⟨e1, e2, e3, e4⟩ := blockMatrixTwoByTwoFin_injective h
  have z : bl hn (0 : Mx D ρ ρ) 0 0 (0 : Mx D p p) = 0 := blockMatrix_zero hn
  have o : bl hn (1 : Mx D ρ ρ) 0 0 (1 : Mx D p p) = 1 := blockRowSubstitution_one hn
  have m : bl hn (-1 : Mx D ρ ρ) 0 0 (-1 : Mx D p p) = -1 := blockMatrix_neg_one hn
  rw [first_block_embedding_block, adjoint_symplectic_block_product]
  simp only [adj_bl, adj_one, adj_zero, block_mul₂, block_sub, bl_add, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, add_zero, zero_add, sub_zero, zero_sub, sub_self, e1, e2, e3, e4, z, o, m]

def firstF (hn : ρ + p = n) (g : G D ρ) : G D n :=
  mkG (Units.map (firstMon hn) (matHom _ D.sp.cm.sig (Jst D ρ) g)) (firstM_isU hn _ (isU_mat g))

theorem matHom_firstF (hn : ρ + p = n) (g : G D ρ) :
    matHom _ D.sp.cm.sig (Jst D n) (firstF hn g) = Units.map (firstMon hn) (matHom _ D.sp.cm.sig (Jst D ρ) g) := rfl

def firstG (hn : ρ + p = n) : G D ρ →* G D n where
  toFun := firstF hn
  map_one' := matHom_injective _ D.sp.cm.sig (Jst D n) (by rw [matHom_firstF, map_one, map_one, map_one])
  map_mul' g h := matHom_injective _ D.sp.cm.sig (Jst D n) (by
    rw [map_mul, matHom_firstF, matHom_firstF, matHom_firstF, map_mul, map_mul])

theorem mat_firstG (hn : ρ + p = n) (h : G D ρ) : mat (firstG hn h) = firstM hn (mat h) := rfl

theorem continuous_firstM (hn : ρ + p = n) : Continuous (firstM (D := D) hn) :=
  continuous_block_matrix (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const
      continuous_const)
    (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const continuous_const)
    (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const continuous_const)
    (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const continuous_const)

theorem continuous_firstG (hn : ρ + p = n) : Continuous (firstG (D := D) hn) := by
  have h0 : Continuous (Units.map (firstMon (D := D) hn : Mx D (ρ + ρ) (ρ + ρ) →* Mx D (n + n) (n + n))) :=
    Continuous.units_map _ (continuous_firstM hn)
  have h : Continuous fun g : G D ρ => Units.map (firstMon (D := D) hn) (matHom _ D.sp.cm.sig (Jst D ρ) g) :=
    h0.comp (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D ρ)).continuous
  exact (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous_iff.2 h

end GlobalTheory.CompanionTheory.FirstBlockEmb

namespace GlobalTheory.CompanionTheory.FirstBlockEmb

theorem exists_first_emb : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n), ∃ ι : G D ρ →* G D n, Continuous ι ∧
  ∀ (h : G D ρ) (a b c d : Mx D ρ ρ), mat h = blk4 a b c d →
    mat (ι h) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1) := by
  intro D n ρ p hn
  refine ⟨firstG hn, continuous_firstG hn, fun h a b c d e => ?_⟩
  exact (mat_firstG hn h).trans ((congrArg (firstM hn) e).trans (first_block_embedding_block hn a b c d))

end GlobalTheory.CompanionTheory.FirstBlockEmb
