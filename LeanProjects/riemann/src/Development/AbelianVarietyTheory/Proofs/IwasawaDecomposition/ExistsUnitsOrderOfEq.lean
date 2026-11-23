import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeWindow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalStageNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedDataCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistEmptyLocalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAutomorphicUnipotentLabelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentThetaDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypesIdempotentCoefficientsStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df

attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.MemN

theorem exists_units_orderOf_eq (p : ℕ) (hp : p.Prime) : ∃ w : (ZMod p)ˣ, orderOf w = p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  refine ⟨w, ?_⟩
  rw [orderOf_eq_card_of_forall_mem_zpowers hw, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime hp]

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial in

theorem exists_nStage_tameChi :
    ∀ (B : Base) (C : Cols B) (W : RowsRest B C), StandIn W → ∃ N : NStage B C W, IsEmpty N.nd.Loc ∧
      ∀ (k : Fin 2) (v : N.nd.PlG k), ∃ w : (ZMod (B.host.g k))ˣ, orderOf w = B.host.g k - 1 ∧
        ∀ j : Fin B.R.m, N.nd.chiT k v j = w ^ (2 * (j.1 + 1)) := by
  intro B C W hS
  choose w hw using fun k : Fin 2 => exists_units_orderOf_eq (B.host.g k) (B.host.g_prime k)
  let χ : Chi B.toPre := fun k _ j => w k ^ (2 * (j.1 + 1))
  have heta : ∀ j w, 1 ≤ j → j ≤ B.R.m → W.etaJ j w = 0 := fun j w _ _ => hS.eta j w
  have hgood : GoodChi B.toPre χ ∨ ((∀ μ, W.eOp μ = 0) ∧ ∀ μ j, W.eMt μ j = 0) := Or.inl (goodChi B.toPre χ)
  obtain ⟨L⟩ := GlobalTheory.T.local_stage_nonempty
  obtain ⟨nd, hE, hχ, -⟩ := GlobalTheory.T.exists_unramified_data_character B C W χ hS.sha
  obtain ⟨tw, hT⟩ := GlobalTheory.T.exists_twist_empty_local B C W nd hE
  obtain ⟨A, hlab, hine⟩ := GlobalTheory.T.exists_automorphic_unipotent_labels B C W nd hE
  obtain ⟨bc⟩ := GlobalTheory.T.base_change_nonempty B.R B.host W.what₂ nd A hE
  obtain ⟨T, hT0, hy⟩ := GlobalTheory.T.exists_types_idempotent_coefficients B C W χ nd A hE hχ hlab hine hgood
  choose e he using hy
  obtain ⟨Y, hY, ⟨th⟩⟩ := GlobalTheory.T.exists_exponent_theta_data B C W nd tw hT e
  obtain ⟨eq, heq⟩ := hχ
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
            etaJ_tie := fun j w h1 h2 => by
              rw [heta j w h1 h2]
              exact (Finset.sum_eq_zero fun i _ => hE.elim i).symm }, hE, ?_⟩
  intro k v
  refine ⟨w k, hw k, fun j => ?_⟩
  show nd.chiT k v j = _
  rw [heq k v]

end GlobalTheory.MemN

end
