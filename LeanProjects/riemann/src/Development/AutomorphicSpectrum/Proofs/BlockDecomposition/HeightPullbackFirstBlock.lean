import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HtPull

open GlobalTheory.CompanionTheory.PcB (blockMatrix_multiply blockMatrix_one)
open GlobalTheory.StdUnn.Model

def leviBl {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (a : GL (Fin ρ) R) : GL (Fin n) R :=
  ⟨bl hn a.1 0 0 1, bl hn (a⁻¹).1 0 0 1,
    by rw [blockMatrix_multiply]; simp [blockMatrix_one], by rw [blockMatrix_multiply]; simp [blockMatrix_one]⟩

theorem det_leviBl {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (a : GL (Fin ρ) R) :
    Matrix.GeneralLinearGroup.det (leviBl hn a) = Matrix.GeneralLinearGroup.det a := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, leviBl, bl]
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem blockMatrix_zero {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 0 = 0 := by
  simp only [bl, Matrix.fromBlocks_zero, Matrix.submatrix_zero, Pi.zero_apply]

theorem blkA_blk4 {R : Type} {k : ℕ} (a b c d : Matrix (Fin k) (Fin k) R) : blkA (blk4 a b c d) = a := by
  ext i j
  simp [blkA, blk4, Matrix.toBlocks₁₁]

theorem isHt_blockPull : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (ι : G D ρ →* G D n), Continuous ι →
  (∀ (h : G D ρ) (a b c d : Mx D ρ ρ), mat h = blk4 a b c d →
    mat (ι h) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1)) →
  ∀ H : G D n → ℝ≥0, IsHt H → IsHt (fun h : G D ρ => H (ι h)) := by
  intro D n ρ p hn ι hc hblk H hH
  refine ⟨hH.1.comp hc, fun g => hH.2.1 _, ?_⟩
  intro q hq a ha g
  obtain ⟨b, d, hm⟩ := GlobalTheory.StdUnn.LeftInvSect.siegelParabolicUnn_matrix_blockUpperTriangular hq
  rw [ha] at hm
  have hι := hblk q a.1 b 0 d hm
  rw [blockMatrix_zero] at hι
  have hqP : ι q ∈ P D n := GlobalTheory.CompanionTheory.SwUnf.SmallCell.mem_siegelParabolic_of_lowerLeft_entries_eq_zero hι
  have hA : blkA (mat (ι q)) = (leviBl hn a).1 := by
    rw [hι, blkA_blk4]
    rfl
  show H (ι (q * g)) = _ * H (ι g)
  rw [map_mul, hH.2.2 _ hqP (leviBl hn a) hA, det_leviBl]

end GlobalTheory.CompanionTheory.HtPull

end
