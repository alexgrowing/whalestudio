import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCosetsParamRational
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelParabolicQuotientIffRowsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryCellBlockNormalFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryBlockInvertibleCriterionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFactorizationRowsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowsProportionalOfTransformStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowsOfWeylHeisenbergProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylHeisenbergLeviRationalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCentreRationalFormStatement
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
theorem _root_.GlobalTheory.T.heisenberg_cosets_param_rational : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (M : Maps D hn),
    ∃ e : ratHerm D ρ × (Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E) → Cosets (P D n) (GF D n),
      Function.Injective e ∧
      (∀ q, zKer hn (ratOf q.out) = ⊥ ↔ q ∈ Set.range e) ∧
      (∀ (l l' : ratHerm D ρ) u (h : M.nzx l'.1 0 ∈ GF D n),
        rmulEquiv (P D n) (GF D n) ⟨M.nzx l'.1 0, h⟩ (e (l, u)) = e (l' + l, u)) ∧
      ∀ f : G D n → ℂ, LeftInv (P D n ⊓ GF D n) f → ∀ (l : ratHerm D ρ) u (y : G D n),
        term (P D n) (GF D n) f y (e (l, u)) =
          f (M.w * M.nzx l.1 0 * M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * y) := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.CellGlue.cell | exact GlobalTheory.CompanionTheory.ZUnf.CellGlue.cell | (intros; apply GlobalTheory.CompanionTheory.ZUnf.CellGlue.cell <;> assumption)
