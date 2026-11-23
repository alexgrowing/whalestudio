import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw

namespace GlobalTheory.CompanionTheory.ZUnf

section Rows

variable {K : Type} [Field K] {n ρ p : ℕ}

def zinc (hn : ρ + p = n) : (Fin ρ → K) →ₗ[K] (Fin n → K) where
  toFun u i := Sum.elim u (fun _ : Fin p => (0 : K)) ((finSumFinEquiv.trans (finCongr hn)).symm i)
  map_add' u v := by
    funext i
    simp only [Pi.add_apply]
    generalize (finSumFinEquiv.trans (finCongr hn)).symm i = j
    rcases j with j | j <;> simp
  map_smul' c u := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    generalize (finSumFinEquiv.trans (finCongr hn)).symm i = j
    rcases j with j | j <;> simp

def wM (hn : ρ + p = n) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (bl hn 0 0 0 1) (bl hn 1 0 0 0) (bl hn (-1) 0 0 0) (bl hn 0 0 0 1)

def nM (hn : ρ + p = n) (ζ : Matrix (Fin ρ) (Fin ρ) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 1 (bl hn ζ 0 0 0) 0 1

def sM (hn : ρ + p = n) (σ : K →+* K) (η : Matrix (Fin ρ) (Fin p) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (bl hn 1 η 0 1) 0 0 (bl hn 1 0 (-cT σ η) 1)

def eM (hn : ρ + p = n) (a b c d : Matrix (Fin p) (Fin p) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d)

def rowC (hn : ρ + p = n) (η : Matrix (Fin ρ) (Fin p) K) (a c : Matrix (Fin p) (Fin p) K) : Matrix (Fin n) (Fin n) K :=
  bl hn (-1) (-(η * a)) 0 c

def rowD (hn : ρ + p = n) (σ : K →+* K) (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K)
    (b d : Matrix (Fin p) (Fin p) K) : Matrix (Fin n) (Fin n) K :=
  bl hn (-ζ) (-(η * b)) (-cT σ η) d

end Rows

variable {D : D7} {n ρ p : ℕ}

def zKer (hn : ρ + p = n) (x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) : Submodule D.host.E (Fin ρ → D.host.E) :=
  (cellKer x).comap (zinc hn)

end GlobalTheory.CompanionTheory.ZUnf
