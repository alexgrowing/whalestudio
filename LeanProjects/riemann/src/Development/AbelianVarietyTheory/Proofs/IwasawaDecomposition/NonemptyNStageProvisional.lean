import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalStageNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedDataCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistEmptyLocalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAutomorphicUnipotentLabelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentThetaDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypesIdempotentCoefficientsStatement

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN

theorem nonempty_nStage_provisional :
    ∀ (B : Base) (C : Cols B) (W : RowsRest B C) (χ : Chi B.toPre), ShaOK B.toPre W.shaLen →
      (∀ j w, 1 ≤ j → j ≤ B.R.m → W.etaJ j w = 0) →
      (GoodChi B.toPre χ ∨ ((∀ μ, W.eOp μ = 0) ∧ ∀ μ j, W.eMt μ j = 0)) → Nonempty (NStage B C W) := by
  intro B C W χ hsha heta hgood
  obtain ⟨L⟩ := GlobalTheory.T.local_stage_nonempty
  obtain ⟨nd, hE, hχ, -⟩ := GlobalTheory.T.exists_unramified_data_character B C W χ hsha
  obtain ⟨tw, hT⟩ := GlobalTheory.T.exists_twist_empty_local B C W nd hE
  obtain ⟨A, hlab, hine⟩ := GlobalTheory.T.exists_automorphic_unipotent_labels B C W nd hE
  obtain ⟨bc⟩ := GlobalTheory.T.base_change_nonempty B.R B.host W.what₂ nd A hE
  obtain ⟨T, hT0, hy⟩ := GlobalTheory.T.exists_types_idempotent_coefficients B C W χ nd A hE hχ hlab hine hgood
  choose e he using hy
  obtain ⟨Y, hY, ⟨th⟩⟩ := GlobalTheory.T.exists_exponent_theta_data B C W nd tw hT e
  refine ⟨{ toLocStage := L
            nd := nd
            ntw := tw
            naut := A
            nbc := bc
            nexp := Y
            ntypes := T
            nStage_trivialCharacter_compat := hT0
            nStage_trivialCharacter_coeff_eq := fun g => by rw [hY]; exact he g
            nth := th
            nbr := fun i => hE.elim i
            nbr_ind := fun i => hE.elim i
            self_good := fun i => hE.elim i
            ntwbr := fun i => hT.elim i
            ntwbr_ind := fun i => hT.elim i
            loc_tie := fun i => hE.elim i
            bc_tie := fun i => hE.elim i
            rbar_tie := fun i => hE.elim i
            mtpar_tie := fun i => hE.elim i
            Z_tie := fun i => hE.elim i
            Zgood_tie := fun i => hE.elim i
            etaJ_tie := fun j w h1 h2 => ?_ }⟩
  rw [heta j w h1 h2]
  exact (Finset.sum_eq_zero fun i _ => hE.elim i).symm

end GlobalTheory.MemN
