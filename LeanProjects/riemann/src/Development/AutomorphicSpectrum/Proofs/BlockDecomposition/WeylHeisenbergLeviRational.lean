import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlockFourMatrices
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

namespace GlobalTheory.CompanionTheory.ZUnf.Rat

variable {D : D7} {n ρ p : ℕ}

theorem blockMatrix_map {R S : Type} {m : ℕ} (f : R → S) (a b c d : Matrix (Fin m) (Fin m) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) :=
  _root_.UpperTheory.Reformulated.B.BlockFourMatrices.main f a b c d

theorem map_bl {R S : Type} (hn : ρ + p = n) (f : R → S) (a : Matrix (Fin ρ) (Fin ρ) R) (b : Matrix (Fin ρ) (Fin p) R)
    (c : Matrix (Fin p) (Fin ρ) R) (d : Matrix (Fin p) (Fin p) R) :
    (bl hn a b c d).map f = bl hn (a.map f) (b.map f) (c.map f) (d.map f) := by
  ext i j
  simp only [bl, Matrix.map_apply, Matrix.submatrix_apply]
  generalize (finSumFinEquiv.trans (finCongr hn)).symm i = x
  generalize (finSumFinEquiv.trans (finCongr hn)).symm j = y
  rcases x with x | x <;> rcases y with y | y <;> simp

theorem map_incA_zero {a b : Type} : (0 : Matrix a b D.host.E).map (incA D) = 0 := by
  ext i j; simp

theorem map_incA_one {m : ℕ} : (1 : Matrix (Fin m) (Fin m) D.host.E).map (incA D) = 1 :=
  map_one (incA D).mapMatrix

theorem map_incA_neg {a b : Type} (x : Matrix a b D.host.E) : (-x).map (incA D) = -(x.map (incA D)) := by
  ext i j; simp

theorem adj_map_incA {a b : ℕ} (x : Matrix (Fin a) (Fin b) D.host.E) :
    adj (x.map (incA D) : Mx D a b) = (cT (D.sp.cm.sig : D.host.E →+* D.host.E) x).map (incA D) := by
  ext i j
  simp only [adj, cT, Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA]
  rfl

theorem adj_zero {a b : ℕ} : adj (0 : Mx D a b) = 0 := by
  ext i j
  simp [adj]

theorem mat_eq : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (M : Maps D hn) (z : hermA D ρ) (ζ : Matrix (Fin ρ) (Fin ρ) D.host.E), ζ.map (incA D) = z.1 →
    ∀ (η : Matrix (Fin ρ) (Fin p) D.host.E) (γ : G D p) (a b c d : Matrix (Fin p) (Fin p) D.host.E), mat γ = (blk4 a b c d).map (incA D) →
    mat (M.w * M.nzx z 0 * M.sh (η.map (incA D)) * M.emb γ) =
      (wM hn * nM hn ζ * sM hn (D.sp.cm.sig : D.host.E →+* D.host.E) η * eM hn a b c d).map (incA D) := by
  intro D n ρ p hn M z ζ hζ η γ a b c d hγ
  have hm : ∀ x y : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E,
      (x * y).map (incA D) = x.map (incA D) * y.map (incA D) := fun x y => Matrix.map_mul
  rw [hm, hm, hm]
  have e1 : mat M.w = (wM hn).map (incA D) := by
    rw [M.w_mat, wM, blockMatrix_map]
    simp only [map_bl, map_incA_zero, map_incA_one, map_incA_neg]
  have e2 : mat (M.nzx z 0) = (nM hn ζ).map (incA D) := by
    rw [M.nzx_mat, nM, blockMatrix_map, adj_zero]
    simp only [map_bl, map_incA_zero, map_incA_one, hζ]
  have e3 : mat (M.sh (η.map (incA D))) = (sM hn (D.sp.cm.sig : D.host.E →+* D.host.E) η).map (incA D) := by
    rw [M.sh_mat, sM, blockMatrix_map, adj_map_incA]
    simp only [map_bl, map_incA_zero, map_incA_one, map_incA_neg]
  have e4 : mat (M.emb γ) = (eM hn a b c d).map (incA D) := by
    have h' := hγ
    rw [blockMatrix_map] at h'
    rw [M.emb_mat γ _ _ _ _ h', eM, blockMatrix_map]
    simp only [map_bl, map_incA_zero, map_incA_one]
  rw [← e1, ← e2, ← e3, ← e4]
  rfl

theorem rat_cell : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (M : Maps D hn) (z : hermA D ρ) (ζ : Matrix (Fin ρ) (Fin ρ) D.host.E), ζ.map (incA D) = z.1 →
    ∀ (η : Matrix (Fin ρ) (Fin p) D.host.E) (γ : GF D p) (a b c d : Matrix (Fin p) (Fin p) D.host.E), mat (γ : G D p) = (blk4 a b c d).map (incA D) →
    M.w * M.nzx z 0 * M.sh (η.map (incA D)) * M.emb (γ : G D p) ∈ GF D n ∧
    mat (M.w * M.nzx z 0 * M.sh (η.map (incA D)) * M.emb (γ : G D p)) =
      (wM hn * nM hn ζ * sM hn (D.sp.cm.sig : D.host.E →+* D.host.E) η * eM hn a b c d).map (incA D) := by
  intro D n ρ p hn M z ζ hζ η γ a b c d hγ
  have h := mat_eq hn M z ζ hζ η γ.1 a b c d hγ
  refine ⟨(GlobalTheory.StdUnn.ChartRat.mem_GF_iff _).2 ⟨_, h.symm⟩, h⟩

end GlobalTheory.CompanionTheory.ZUnf.Rat
