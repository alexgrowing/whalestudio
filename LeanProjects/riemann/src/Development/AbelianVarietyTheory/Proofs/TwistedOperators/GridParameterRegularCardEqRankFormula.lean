import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridMinimalGapEqChiGridGapGammaOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Finset

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridParDCount

variable (D : D7) (C : ℝ) (τ : D.what₂.Tau)

local notation "Γ" => num D C τ

theorem card_Ms_le {j : ℕ} (hj : j ≤ D.R.m) : ((Icc 1 j).biUnion (Γ).blockM).card = j * D.R.t := by
  rw [card_biUnion]
  · have : ∀ u ∈ Icc 1 j, ((Γ).blockM u).card = D.R.t := fun u _ => card_block _ _
    rw [sum_congr rfl this, sum_const, Nat.card_Icc, smul_eq_mul]
    congr 1
  · intro u hu v hv huv
    have hu := mem_Icc.1 hu
    have hv := mem_Icc.1 hv
    refine disjoint_left.2 fun x h1 h2 => ?_
    obtain ⟨a1, a2⟩ := GlobalTheory.FunObj.blockM_bd D C τ h1
    obtain ⟨b1, b2⟩ := GlobalTheory.FunObj.blockM_bd D C τ h2
    rcases lt_or_gt_of_ne huv with h | h
    · linarith [GlobalTheory.FunObj.num_e_lt D C τ hu.1 h (hv.2.trans hj)]
    · linarith [GlobalTheory.FunObj.num_e_lt D C τ hv.1 h (hu.2.trans hj)]

theorem Ms_sub {j : ℕ} (hj : j ≤ D.R.m) : (Icc 1 j).biUnion (Γ).blockM ⊆ (Icc 1 (Γ).m).biUnion (Γ).blockM :=
  biUnion_subset_biUnion_of_subset_left _ (Icc_subset_Icc le_rfl hj)

theorem card_entries_parD {i j : ℕ} (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) :
    (entries ((Γ).parD i j)).card = rankV D i j := by
  have d1 : Disjoint (Γ).cloud (Γ).lows := disjoint_left.2 fun x h1 h2 => by
    linarith [(GlobalTheory.FunObj.cloud_gt D C τ h1).1, GlobalTheory.FunObj.lows_le D C τ h2]
  have d2 : Disjoint ((Γ).cloud ∪ (Γ).lows) ((Icc 1 j).biUnion (Γ).blockM) := by
    refine disjoint_union_left.2 ⟨disjoint_left.2 fun x h1 h2 => ?_,
      (GlobalTheory.FunObj.disj_lows_Ms D C τ).mono_right (Ms_sub D C τ hj)⟩
    linarith [(GlobalTheory.FunObj.cloud_gt D C τ h1).1, GlobalTheory.FunObj.Ms_lt D C τ (Ms_sub D C τ hj h2)]
  have d3 : Disjoint ((Γ).cloud ∪ (Γ).lows ∪ (Icc 1 j).biUnion (Γ).blockM)
      ((Icc ((Γ).m - i + 1) (Γ).m).biUnion (Γ).blockC) := by
    refine disjoint_left.2 fun x h1 h2 => ?_
    obtain ⟨u, hu, h2⟩ := mem_biUnion.1 h2
    have hu := mem_Icc.1 hu
    have hb := (GlobalTheory.FunObj.blockC_bd D C τ (by omega) hu.2 h2).1
    have ha := GlobalTheory.FunObj.a_le D C τ hu.2
    have : x < (Γ).a (Γ).m := by
      rcases mem_union.1 h1 with h1 | h1
      · rcases mem_union.1 h1 with h1 | h1
        · exact (GlobalTheory.FunObj.cloud_gt D C τ h1).2
        · exact GlobalTheory.FunObj.low_lt_a D C τ (GlobalTheory.FunObj.lows_le D C τ h1)
      · exact GlobalTheory.FunObj.low_lt_a D C τ (GlobalTheory.FunObj.Ms_lt D C τ (Ms_sub D C τ hj h1)).le
    linarith
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  rw [GridData.entries_parD, card_union_of_disjoint d3, card_union_of_disjoint d2, card_union_of_disjoint d1,
    GlobalTheory.FunObj.card_cloud, GlobalTheory.FunObj.card_lows, card_Ms_le D C τ hj, GlobalTheory.FunObj.card_Cs D C τ hi]
  simp only [rankV, Ranks.r]
  omega

theorem card_parD {i j : ℕ} (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : ((Γ).parD i j).card = rankV D i j := by
  refine le_antisymm ?_ ((card_entries_parD D C τ hi hj).symm.le.trans card_image_le)
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have e : rankV D i j = (D.R.k - 1) + D.R.m + j * D.R.t + i * sLen D := by
    simp only [rankV, Ranks.r]
    omega
  rw [e, GridData.parD]
  refine (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans
    (add_le_add ?_ ?_)) ?_)) ?_)
  · exact card_image_le.trans (GlobalTheory.FunObj.card_cloud D C τ).le
  · refine card_image_le.trans ?_
    rw [Nat.card_Icc]
    show D.R.m + 1 - 1 ≤ D.R.m
    omega
  · exact card_image_le.trans (card_Ms_le D C τ hj).le
  · exact card_image_le.trans (GlobalTheory.FunObj.card_Cs D C τ hi).le

theorem isRegular_parD {i j : ℕ} (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : IsRegular ((Γ).parD i j) :=
  isRegular_iff_card.2 ((card_entries_parD D C τ hi hj).trans (card_parD D C τ hi hj).symm)

theorem grid_eq_num (τ : D.what₂.Tau) : GlobalTheory.Grid.grid D τ = num D 1 τ := by
  have h := GlobalTheory.GridJoin.gap_eq_chiGap D
  unfold GlobalTheory.Grid.grid GlobalTheory.Grid.gridOf GlobalTheory.Grid.cen num GlobalTheory.ChiGrid.cen
  rw [h]
  rfl

theorem parD_regular_card : ∀ (D : D7), HostHyp D → ∀ (τ : D.what₂.Tau) (i j : ℕ), 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m →
    GlobalTheory.SignedHC.IsRegular ((GlobalTheory.Grid.grid D τ).parD i j) ∧ ((GlobalTheory.Grid.grid D τ).parD i j).card = GlobalTheory.Grid.rkV D i j := by
  intro D _ τ i j _ hi hj
  rw [grid_eq_num D τ]
  exact ⟨isRegular_parD D 1 τ hi hj, card_parD D 1 τ hi hj⟩

end GlobalTheory.GridParDCount
