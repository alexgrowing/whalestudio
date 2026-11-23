import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelParabolicQuotientIffRows
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_parabolic_quotient_iff_rows : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n : ℕ} (x r : Matrix (Fin (n + n)) (Fin (n + n)) K),
    IsUnit r.det → IsUnitary σ (blk4 0 1 (-1) 0) x → IsUnitary σ (blk4 0 1 (-1) 0) r →
    (IsSiegelP (x * r⁻¹) ↔ ∃ T : Matrix (Fin n) (Fin n) K, lowerC x = T * lowerC r ∧ GlobalTheory.CompanionTheory.RatPtsUnn.blkD x = T * GlobalTheory.CompanionTheory.RatPtsUnn.blkD r) := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.siegel_mul_inv_iff_rows | exact GlobalTheory.CompanionTheory.ZUnf.siegel_mul_inv_iff_rows | (intros; apply GlobalTheory.CompanionTheory.ZUnf.siegel_mul_inv_iff_rows <;> assumption)
