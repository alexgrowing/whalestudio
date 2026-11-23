import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.LawW

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.PcB

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

def qm (hn : ρ + p = n) (x : Mx D ρ p) : Mx D (n + n) (n + n) :=
  blk4 (bl hn 1 0 (adj x) 1) 0 0 (bl hn 1 (-x) 0 1)

theorem qm_mul_w (M : Maps D hn) (x : Mx D ρ p) :
    qm hn x * mat M.w = mat M.w * mat (M.nzx 0 x) := by
  rw [M.w_mat, M.nzx_mat, qm, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  have hz : ((0 : hermA D ρ).1 : Mx D ρ ρ) = 0 := rfl
  rw [hz]
  simp only [blockMatrix_multiply]
  congr 1 <;> simp
  · rw [blockMatrix_add']; simp
  · rw [blockMatrix_add']; simp

theorem mat_conj (M : Maps D hn) (x : Mx D ρ p) : mat (M.w * M.nzx 0 x * M.w⁻¹) = qm hn x := by
  have h : mat M.w * mat M.w⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  calc mat (M.w * M.nzx 0 x * M.w⁻¹) = (mat M.w * mat (M.nzx 0 x)) * mat M.w⁻¹ := rfl
    _ = qm hn x * (mat M.w * mat M.w⁻¹) := by rw [← qm_mul_w, mul_assoc]
    _ = qm hn x := by rw [h, mul_one]

theorem exists_low (hn : ρ + p = n) (c : Mx D p ρ) :
    ∃ a : GL (Fin n) (AE D), a.1 = bl hn 1 0 c 1 :=
  ⟨⟨bl hn 1 0 c 1, bl hn 1 0 (-c) 1, by rw [lowerUnipotent_mul, add_neg_cancel, blockMatrix_one], by rw [lowerUnipotent_mul, neg_add_cancel, blockMatrix_one]⟩, rfl⟩

theorem det_low (hn : ρ + p = n) (c : Mx D p ρ) (a : GL (Fin n) (AE D)) (ha : a.1 = bl hn 1 0 c 1) :
    Matrix.GeneralLinearGroup.det a = 1 := by
  apply Units.ext
  change a.1.det = 1
  rw [ha, bl, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]
  simp

theorem blkA_qm (hn : ρ + p = n) (x : Mx D ρ p) : blkA (qm hn x) = bl hn 1 0 (adj x) 1 := by
  ext i j
  simp [qm, blkA, blk4, Matrix.toBlocks₁₁]

theorem law_w : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ),
    IsLaw χ s f → ∀ (x : Mx D ρ p) (h : G D n), f (M.w * M.nzx 0 x * h) = f (M.w * h) := by
  intro D n ρ p hn M χ s f hf x h
  have hq := mat_conj M x
  have hP : M.w * M.nzx 0 x * M.w⁻¹ ∈ P D n := GlobalTheory.CompanionTheory.SwUnf.SmallCell.mem_siegelParabolic_of_lowerLeft_entries_eq_zero hq
  obtain ⟨a, ha⟩ := exists_low hn (adj x)
  have hA : blkA (mat (M.w * M.nzx 0 x * M.w⁻¹)) = a.1 := by rw [hq, blkA_qm, ha]
  have key := hf _ hP a hA (M.w * h)
  rw [det_low hn (adj x) a ha, map_one, map_one] at key
  have e : M.w * M.nzx 0 x * M.w⁻¹ * (M.w * h) = M.w * M.nzx 0 x * h := by group
  rw [e] at key
  simpa using key

end GlobalTheory.CompanionTheory.FJE.LawW
