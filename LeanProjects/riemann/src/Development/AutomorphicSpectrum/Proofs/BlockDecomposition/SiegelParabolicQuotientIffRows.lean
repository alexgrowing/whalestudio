import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.SRows

theorem blkD_siegel_mul {K : Type} [Field K] {n : ℕ} {y : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hy : IsSiegelP y) (W : Matrix (Fin (n + n)) (Fin (n + n)) K) :
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (y * W) = GlobalTheory.CompanionTheory.RatPtsUnn.blkD y * GlobalTheory.CompanionTheory.RatPtsUnn.blkD W := by
  ext i j
  change (y * W) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = _
  rw [Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type, Matrix.mul_apply]
  have h0 : ∑ k : Fin n, y (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl k)) *
      W (finSumFinEquiv (Sum.inl k)) (finSumFinEquiv (Sum.inr j)) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hy i k, zero_mul]
  rw [h0, zero_add]
  rfl

theorem inverse_unitary_block_form {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {a b c d : Matrix (Fin n) (Fin n) K}
    (h : IsUnitary σ (blk4 0 1 (-1) 0) (blk4 a b c d)) :
    (blk4 a b c d)⁻¹ = blk4 (cT σ d) (-cT σ b) (-cT σ c) (cT σ a) := by
  have hJJ' : (blk4 0 (-1) 1 0 : Matrix (Fin (n + n)) (Fin (n + n)) K) * blk4 0 1 (-1) 0 = 1 := by
    rw [submatrix_fromBlocks_mul]
    simp [GlobalTheory.CompanionTheory.SwUnf.BigCell.block_identity_eq_one]
  have h0 : cT σ (blk4 a b c d) * blk4 0 1 (-1) 0 * blk4 a b c d = blk4 0 1 (-1) 0 := h
  have h1 : (blk4 0 (-1) 1 0 * cT σ (blk4 a b c d) * blk4 0 1 (-1) 0) * blk4 a b c d = 1 := by
    rw [mul_assoc (blk4 0 (-1) 1 0), mul_assoc (blk4 0 (-1) 1 0), h0, hJJ']
  rw [Matrix.inv_eq_left_inv h1, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp

end GlobalTheory.CompanionTheory.ZUnf.SRows

theorem GlobalTheory.CompanionTheory.ZUnf.siegel_mul_inv_iff_rows : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n : ℕ} (x r : Matrix (Fin (n + n)) (Fin (n + n)) K),
    IsUnit r.det → IsUnitary σ (blk4 0 1 (-1) 0) x → IsUnitary σ (blk4 0 1 (-1) 0) r →
    (IsSiegelP (x * r⁻¹) ↔ ∃ T : Matrix (Fin n) (Fin n) K, lowerC x = T * lowerC r ∧ GlobalTheory.CompanionTheory.RatPtsUnn.blkD x = T * GlobalTheory.CompanionTheory.RatPtsUnn.blkD r) := by
  intro K _ σ _ n x r hr hx hrU
  obtain ⟨a, b, hr4⟩ := GlobalTheory.CompanionTheory.SwUnf.BigCell.exists_blockMatrixTwoByTwoFin_eq r
  constructor
  · intro h
    have e : x = (x * r⁻¹) * r := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hr, Matrix.mul_one]
    refine ⟨GlobalTheory.CompanionTheory.RatPtsUnn.blkD (x * r⁻¹), ?_, ?_⟩
    · conv_lhs => rw [e]
      exact GlobalTheory.CompanionTheory.SwUnf.lowerC_siegel_mul h r
    · conv_lhs => rw [e]
      exact GlobalTheory.CompanionTheory.ZUnf.SRows.blkD_siegel_mul h r
  · rintro ⟨T, h1, h2⟩
    rw [GlobalTheory.CompanionTheory.SwUnf.BigCell.isSiegelParabolic_iff]
    obtain ⟨a', b', hx4⟩ := GlobalTheory.CompanionTheory.SwUnf.BigCell.exists_blockMatrixTwoByTwoFin_eq x
    have hU' : IsUnitary σ (blk4 0 1 (-1) 0)
        (blk4 a b (lowerC r) (GlobalTheory.CompanionTheory.RatPtsUnn.blkD r)) := by
      rw [← hr4]; exact hrU
    have hinv := GlobalTheory.CompanionTheory.ZUnf.SRows.inverse_unitary_block_form σ hU'
    rw [← hr4] at hinv
    have hrel := GlobalTheory.CompanionTheory.SwUnf.BigCell.lower_rel σ hU'
    have e : lowerC (x * r⁻¹) = lowerC x * cT σ (GlobalTheory.CompanionTheory.RatPtsUnn.blkD r)
        - GlobalTheory.CompanionTheory.RatPtsUnn.blkD x * cT σ (lowerC r) := by
      rw [hinv]
      conv_lhs => rw [hx4]
      rw [submatrix_fromBlocks_mul, GlobalTheory.CompanionTheory.SwUnf.BigCell.lowerLeft_block]
      simp [sub_eq_add_neg]
    rw [e, h1, h2, mul_assoc, mul_assoc, hrel, sub_self]
