import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylHeisenbergLeviRational
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
theorem _root_.GlobalTheory.T.weyl_heisenberg_levi_rational : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (M : Maps D hn) (z : hermA D ρ) (ζ : Matrix (Fin ρ) (Fin ρ) D.host.E), ζ.map (incA D) = z.1 →
    ∀ (η : Matrix (Fin ρ) (Fin p) D.host.E) (γ : GF D p) (a b c d : Matrix (Fin p) (Fin p) D.host.E), mat (γ : G D p) = (blk4 a b c d).map (incA D) →
    M.w * M.nzx z 0 * M.sh (η.map (incA D)) * M.emb (γ : G D p) ∈ GF D n ∧
    mat (M.w * M.nzx z 0 * M.sh (η.map (incA D)) * M.emb (γ : G D p)) =
      (wM hn * nM hn ζ * sM hn (D.sp.cm.sig : D.host.E →+* D.host.E) η * eM hn a b c d).map (incA D) := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.Rat.rat_cell | exact GlobalTheory.CompanionTheory.ZUnf.Rat.rat_cell | (intros; apply GlobalTheory.CompanionTheory.ZUnf.Rat.rat_cell <;> assumption)
