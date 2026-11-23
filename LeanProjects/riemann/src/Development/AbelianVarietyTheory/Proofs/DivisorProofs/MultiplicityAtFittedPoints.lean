import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
import Development.AbelianVarietyTheory.Definitions.Divisors.NotLeafMMZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlopeEHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.TreeLeafParameterArithmeticOfBounds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PtFieldMain

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest

namespace GlobalTheory.BigTop.Fun.LeafMMTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Spread

open GlobalTheory.SignedHC

variable (D : D7) (C : ℝ) (τ : D.what₂.Tau)

theorem weightX_zero_bounds {x : ℚ} (hx : x ∈ (num D C τ).weightX 0) :
    ((num D C τ).v D.R.k : ℚ) - 1 / 2 ≤ x ∧ x ≤ (num D C τ).a 0 := by
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hg : (0 : ℚ) ≤ (num D C τ).ga := by positivity
  have hvk := v_le_two D C τ hk le_rfl
  have ham : (num D C τ).a (num D C τ).m = (num D C τ).v 2 + (num D C τ).ga + 1 / 2 := (num D C τ).a_m
  have hlow : ∀ i, i ≤ D.R.m → ((num D C τ).v D.R.k : ℚ) - 1 / 2 ≤ (num D C τ).a i := fun i hi => by
    have := a_le D C τ hi
    have e : (num D C τ).m = D.R.m := rfl
    rw [e] at ham
    linarith
  have h0 : ((num D C τ).v 2 : ℚ) + 1 / 2 ≤ (num D C τ).a 0 := by
    have h1 := a_le D C τ (Nat.zero_le D.R.m)
    have e : (num D C τ).m = D.R.m := rfl
    rw [e] at ham
    linarith
  rcases GridData.mem_weightX.1 hx with h | h | ⟨i, h1, h2, h⟩ | ⟨l, h1, h2, -⟩
  · obtain ⟨i, hi, rfl⟩ := GridData.mem_tops.1 h
    exact ⟨hlow i hi, a_le D C τ (Nat.zero_le i)⟩
  · obtain ⟨i, h1, h2, rfl⟩ := GridData.mem_cloudHalf.1 h
    have hi := v_le_two D C τ h1 h2
    have hik : ((num D C τ).v D.R.k : ℚ) ≤ (num D C τ).v i := by
      rcases h2.eq_or_lt with e | e
      · rw [e]; exact le_rfl
      · exact_mod_cast ((num D C τ).v_anti i D.R.k h1 e le_rfl).le
    simp only [GridData.vHalf]
    constructor <;> linarith
  · have hb := blockC'_between (num_nearMid D C τ) (odd_sLen D).pos (sLen_lt_gap D C) h1 h2 h
    have hp := (num D C τ).a_pred h1
    have hq := a_le D C τ (Nat.zero_le (i - 1))
    exact ⟨(hlow i h2).trans hb.1.le, by linarith [hb.2]⟩
  · omega

theorem La_sub_le (i j : Fin (rankP D D.R.m)) :
    (((La D C τ).w i - (La D C τ).w j : ℤ) : ℚ) ≤
      (((num D C τ).v 2 - (num D C τ).v D.R.k : ℤ) : ℚ) + 1 + ((D.R.m : ℚ) + 1) * (gap D C : ℚ) + (rankP D D.R.m : ℚ) := by
  push_cast
  rw [La_cast, La_cast]
  simp only [highestWeight]
  have hi := weightX_zero_bounds D C τ (descEnum_mem _ (card_weight D C τ) i)
  have hj := weightX_zero_bounds D C τ (descEnum_mem _ (card_weight D C τ) j)
  have ea : (num D C τ).a 0 = (num D C τ).v 2 + 1 / 2 + ((D.R.m : ℚ) + 1 - ((0 : ℕ) : ℚ)) * (gap D C : ℚ) := rfl
  have hi' : ((i : ℕ) : ℚ) ≤ (rankP D D.R.m : ℚ) := by exact_mod_cast i.2.le
  have hj' : (0 : ℚ) ≤ ((j : ℕ) : ℚ) := by positivity
  rw [ea] at hi hj
  push_cast at hi hj
  linarith [hi.1, hi.2, hj.1, hj.2]

end Spread

section Leaf

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem np_eq {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF) : ((rankP D D.R.m : ℕ) : ℝ) = d.O.np := by
  have hm := D.R.two_le_m
  have e1 : D.R.r + 6 - 1 = D.R.k + D.R.m + 4 := by unfold Ranks.r; omega
  have e2 : D.R.r + 1 = D.R.k + D.R.m := by unfold Ranks.r; omega
  have e : rankP D D.R.m = (D.R.k + D.R.m) + D.R.m * (D.R.k + D.R.m + 4) := by
    unfold rankP nRk sLen
    rw [e1, e2]
  rw [e]
  show _ = ((D.R.k : ℝ) + D.R.m - 1 + 1) + D.R.m * (((D.R.k : ℝ) + D.R.m - 1) + 5)
  push_cast
  ring

theorem leafMM_of_test {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF) (a : SlopeTestRemainingChoices p d.G d.W d.n) (h : TieTest d a) {C : ℝ}
    (hC : 1 ≤ C) : Formalism.L2.Indef.Tree.LeafMM d.O C := by
  obtain ⟨v₀, hv⟩ := (GlobalTheory.ptField_main D).2.1
  have hga : (gap D 1 : ℝ) ≤ d.O.ga C := by
    rw [← GlobalTheory.BigTop.Fun.Model.ga_eq d 1]
    exact_mod_cast GlobalTheory.SizeLeafCheck.ga_mono _ hC
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) + 1 := by positivity
  have hRp : d.O.Rp C = ((D.R.m : ℝ) + 1) * ((d.O.ga C : ℝ) + 1) + d.O.Lc + d.O.np := rfl
  have hnp : (0 : ℝ) ≤ d.O.np := by rw [← np_eq d]; positivity
  have hR1 : 1 ≤ d.O.Rp C := by
    rw [hRp]
    have : (1 : ℝ) ≤ ((D.R.m : ℝ) + 1) * ((d.O.ga C : ℝ) + 1) := by
      have h1 : (1 : ℝ) ≤ (D.R.m : ℝ) + 1 := by linarith [(Nat.cast_nonneg D.R.m : (0 : ℝ) ≤ D.R.m)]
      have h2 : (1 : ℝ) ≤ (d.O.ga C : ℝ) + 1 := by linarith [(Nat.cast_nonneg (d.O.ga C) : (0 : ℝ) ≤ d.O.ga C)]
      nlinarith
    have : (0 : ℝ) ≤ d.O.Lc := Nat.cast_nonneg _
    linarith
  have hSp : GlobalTheory.TestLat.SpreadLe (LaP d.G) (d.O.Rp C) := by
    intro τ i j
    show (((La D 1 τ).w (Fin.cast (rank_Xp d.G) i) - (La D 1 τ).w (Fin.cast (rank_Xp d.G) j) : ℤ) : ℝ) ≤ _
    have hq := La_sub_le D 1 τ (Fin.cast (rank_Xp d.G) i) (Fin.cast (rank_Xp d.G) j)
    have hr := (Rat.cast_le (K := ℝ)).2 hq
    push_cast at hr
    have hL : ((num D 1 τ).v 2 - (num D 1 τ).v D.R.k).toNat ≤ cloudLen D :=
      Finset.le_sup (f := fun τ => ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 -
        (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k).toNat) (Finset.mem_univ τ)
    have hL' : (((num D 1 τ).v 2 : ℝ) - (num D 1 τ).v D.R.k) ≤ d.O.Lc := by
      rw [GlobalTheory.BigTop.Fun.Model.Lc_eq d]
      have h1 := Int.self_le_toNat ((num D 1 τ).v 2 - (num D 1 τ).v D.R.k)
      have h2 : (((num D 1 τ).v 2 - (num D 1 τ).v D.R.k : ℤ) : ℝ) ≤ (((num D 1 τ).v 2 - (num D 1 τ).v D.R.k).toNat : ℤ) := by
        exact_mod_cast h1
      have h3 : ((((num D 1 τ).v 2 - (num D 1 τ).v D.R.k).toNat : ℕ) : ℝ) ≤ (cloudLen D : ℝ) := by exact_mod_cast hL
      push_cast at h2
      linarith
    have hmul := mul_le_mul_of_nonneg_left (by linarith : (gap D 1 : ℝ) + 1 ≤ (d.O.ga C : ℝ) + 1) hm0
    have hexp : ((D.R.m : ℝ) + 1) * ((gap D 1 : ℝ) + 1) = ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) + ((D.R.m : ℝ) + 1) := by ring
    have hm1 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
    rw [hRp, ← np_eq d]
    push_cast
    linarith
  obtain ⟨h1, h2, h3, h4⟩ := IsTestLat.gridTestLattice_largestSlope_bound GlobalTheory.TestLat.slope_holds.2 hv hR1 hSp h
  refine ⟨h1, h2, h3, h4.trans (le_of_eq ?_)⟩
  unfold GlobalTheory.TestLat.bound Formalism.L2.Indef.Tree.FunData.EMM
  rw [rank_Xp, np_eq d, D.what₂.card_Tau]
  rfl

end Leaf

theorem mm_tie : GlobalTheory.BigTop.Fun.SetAt → GlobalTheory.BigTop.Fun.MM @GlobalTheory.BigTop.Fun.Comparison₂ := fun h =>
  ⟨0, fun _ _ => h.imp fun _ _ _ _ _ => ⟨1, fun _ hC => EvPt.of_forall fun _ _ _ _ _ d hd =>
    let ⟨_, a, ha⟩ := hd
    leafMM_of_test d a ha.test hC⟩⟩

end GlobalTheory.BigTop.Fun.LeafMMTie
