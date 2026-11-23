import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
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

namespace GlobalTheory.CompanionTheory.ZUnf.Centre

open GlobalTheory.CompanionTheory.PcB

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem centre_commutes_embedded_block {R : Type} [CommRing R] (hn : ρ + p = n) (z : Matrix (Fin ρ) (Fin ρ) R)
    (a b c d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (blk4 1 (bl hn z 0 0 0) 0 1)
        (blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d)) =
      HMul.hMul (blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d))
        (blk4 1 (bl hn z 0 0 0) 0 1) := by
  have h1 : HMul.hMul (bl hn z 0 0 0) (bl hn 0 0 0 c) = 0 := by
    rw [blockMatrix_multiply]
    simp [bl]
  have h2 : HMul.hMul (bl hn z 0 0 0) (bl hn 1 0 0 d) = bl hn z 0 0 0 := by
    rw [blockMatrix_multiply]
    simp
  have h3 : HMul.hMul (bl hn 1 0 0 a) (bl hn z 0 0 0) = bl hn z 0 0 0 := by
    rw [blockMatrix_multiply]
    simp
  have h4 : HMul.hMul (bl hn 0 0 0 c) (bl hn z 0 0 0) = 0 := by
    rw [blockMatrix_multiply]
    simp [bl]
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, h1, h2, h3, h4]
  congr 1 <;> simp [add_comm]

theorem nzx_add (M : Maps D hn) (a b : hermA D ρ) : M.nzx (a + b) 0 = M.nzx a 0 * M.nzx b 0 := by
  rw [nzx_mul, add_zero]

theorem nzx_comm_sh (M : Maps D hn) (z : hermA D ρ) (y : Mx D ρ p) :
    M.nzx z 0 * M.sh y = M.sh y * M.nzx z 0 := by
  have h : tw z 0 y = z := by
    apply Subtype.ext
    simp [tw]
  have e := nzx_sh M z 0 y
  rwa [h] at e

theorem nzx_comm_emb (M : Maps D hn) (z : hermA D ρ) (h : G D p) :
    M.nzx z 0 * M.emb h = M.emb h * M.nzx z 0 := by
  obtain ⟨b, d, hb⟩ := SmallCell.exists_blocks (mat h)
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [mat_mul', mat_mul', M.nzx_mat, M.emb_mat h _ _ _ _ hb, adj_zero]
  exact centre_commutes_embedded_block hn z.1 _ _ _ _

theorem nzx_rat_mat (M : Maps D hn) (l : ratHerm D ρ) :
    ∃ ζ : Matrix (Fin ρ) (Fin ρ) D.host.E,
      ζ.map (incA D) = l.1.1 ∧ mat (M.nzx l.1 0) = blk4 1 ((bl hn ζ 0 0 0).map (incA D)) 0 1 := by
  obtain ⟨b, hb⟩ := BigCell.exists_hermQ l
  have e : ∀ {a c : ℕ}, (0 : Matrix (Fin a) (Fin c) D.host.E).map (incA D) = 0 := rat_zero'
  refine ⟨b.1, hb, ?_⟩
  rw [blockMatrix_map₂, hb, e, e, e, M.nzx_mat, adj_zero]

theorem nzx_mem_GF (M : Maps D hn) (l : ratHerm D ρ) : M.nzx l.1 0 ∈ GF D n := by
  have h := nzx_rat M l.1 l.2 0
  rwa [rat_zero'] at h

end GlobalTheory.CompanionTheory.ZUnf.Centre

namespace GlobalTheory.CompanionTheory.ZUnf

theorem centre_nzx : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn),
    (∀ a b, M.nzx (a + b) 0 = M.nzx a 0 * M.nzx b 0) ∧ (∀ z y, M.nzx z 0 * M.sh y = M.sh y * M.nzx z 0) ∧
    (∀ z h, M.nzx z 0 * M.emb h = M.emb h * M.nzx z 0) ∧
    ∀ l : ratHerm D ρ, M.nzx l.1 0 ∈ GF D n ∧ ∃ ζ : Matrix (Fin ρ) (Fin ρ) D.host.E,
      ζ.map (incA D) = l.1.1 ∧ mat (M.nzx l.1 0) = blk4 1 ((bl hn ζ 0 0 0).map (incA D)) 0 1 :=
  fun M => ⟨Centre.nzx_add M, Centre.nzx_comm_sh M, Centre.nzx_comm_emb M,
    fun l => ⟨Centre.nzx_mem_GF M l, Centre.nzx_rat_mat M l⟩⟩

end GlobalTheory.CompanionTheory.ZUnf
