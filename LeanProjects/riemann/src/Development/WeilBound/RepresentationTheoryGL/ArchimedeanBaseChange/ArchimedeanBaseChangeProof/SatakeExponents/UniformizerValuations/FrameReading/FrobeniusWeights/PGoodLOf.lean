import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.WeightLOf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem v_one_of_ordL {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} (u : (w.adicCompletion E)ˣ)
    (h : ordL (u : w.adicCompletion E) = 0) : Valued.v (u : w.adicCompletion E) = 1 := by
  have h0 : Valued.v (u : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).2 u.ne_zero
  unfold ordL at h
  rw [dif_neg h0, neg_eq_zero] at h
  have h1 : WithZero.unzero h0 = 1 := by simpa using congrArg Multiplicative.ofAdd h
  rw [← WithZero.coe_unzero h0, h1]
  rfl

theorem goodLOf_holds : GoodLOf := by
  intro hRS hFm hAct hLoc hCF hUS hCt E _ _ _ hE n a ha π hπ μ e hμ Sec hSec d hd hPS hdμ hϖ hunr σ hσ l₁ l₂ μ₁ μ₂ μa μb A s₁ s₂ Pa Pb D hC hL1 hL2
    I G hG0 hGs hGl hact
  obtain ⟨j, hj⟩ : ∃ j, G j ≠ 0 := by
    by_contra h
    push Not at h
    exact hG0 (funext h)
  have hab : a + (n - a) = n := Nat.add_sub_of_le ha
  have core : ∀ w ∈ Sec, IsSplitAt w → w ∉ d.T → w ∉ d.S₀ → w ∉ d.Bad →
      D.SplitAt π w ∧ ∀ u, ConjPl w u → D.SplitAt π u := by
    intro w hwS hw hT hS0 hBad
    have hun : μ.UnrAt w := hunr w hwS hS0 hBad
    have hgood : d.Good w := ⟨hw, hT, hS0, hBad, fun u hu => by rw [hdμ w]; exact hun u (v_one_of_ordL u hu)⟩
    have hlev : d.lev a w = K2 a (n - a) w := by simp [LocData.lev, hT, hS0, hBad]
    have hlev2 : d.lev₂ a w = K2 a (n - a) w := by simp [LocData.lev₂, hS0, hBad]
    have hKU : d.KU w = KL n w := by simp [LocData.KU, hT, hS0, hBad]
    obtain ⟨hfix1, hfix2⟩ := (hGl j).2 w hwS
    rw [hlev] at hfix1
    have hfix2' := hfix2 hw
    rw [hlev2] at hfix2'
    have hCtk := fun k => hCt E n a (n - a) hab w (d.μ w) (d.ϖ w) k hw (hϖ w) hgood.2.2.2.2
    have hsgn : d.sgn a w = 1 := by
      simp only [LocData.sgn]
      rw [(hCtk 0).2.2]
      simp
    have hhc : ∀ k, d.hc a ha w k = ctT hab w (d.μ w) (d.ϖ w) k := by
      intro k
      simp [LocData.hc, hsgn]
    have hOk : ∀ k intersection_update_fsHerm_neg_one, (d.hL a ha w k intersection_update_fsHerm_neg_one).Ok d.P := fun k intersection_update_fsHerm_neg_one =>
      (hLoc E n d hd a ha).2.2.2 _ (Or.inr ⟨w, k, intersection_update_fsHerm_neg_one, hgood, rfl⟩)
    have hDI : ∀ k intersection_update_fsHerm_neg_one, DiagIdem d.P (d.lev a) (d.hL a ha w k intersection_update_fsHerm_neg_one) := by
      intro k intersection_update_fsHerm_neg_one w' _ x y
      simp only [LocData.hL, LocData.eL, LocData.diag]
      split_ifs <;> rfl
    have hwP : w ∉ d.P := by simp [LocData.P, hT, hS0]
    have hP : ∀ k, actP w (ctT hab w (d.μ w) (d.ϖ w) k) (G j) =
        twTr (σ w).ρ (KL n w) (KL n w) (d.hU w k) LinearMap.id • G j := by
      intro k
      have h1 := (hFm E d.kap Sec d.P (A.blk _) (Equiv.refl _) hSec hPS (d.lev a) (d.lev₂ a) (d.hL a ha w k false) I G w
        hL1 hL2 (hOk k false) (hDI k false) hGl hwS).1 hwP
        (fun w' hw' => by simp only [LocData.hL, LocData.eL, Bool.false_eq_true, ite_false]; rw [Function.update_of_ne hw']; rfl)
        (fun w' => by simp only [LocData.hL, LocData.eL, Bool.false_eq_true, ite_false]; rfl) j
      have h2 := congrFun (hact w hwS hgood k false) j
      have h3 : (d.hL a ha w k false).s w = ctT hab w (d.μ w) (d.ϖ w) k := by
        simp [LocData.hL, hhc]
      rw [h3] at h1
      rw [← h1]
      exact h2
    have hT' : ∀ k, actT w (ctT hab w (d.μ w) (d.ϖ w) k) (G j) =
        twTr (σ w).ρ (KL n w) (KL n w) (d.hU w k) LinearMap.id • G j := by
      intro k
      have h1 := (hFm E d.kap Sec d.P (A.blk _) (Equiv.refl _) hSec hPS (d.lev a) (d.lev₂ a) (d.hL a ha w k true) I G w
        hL1 hL2 (hOk k true) (hDI k true) hGl hwS).2 hw
        (fun w' => by simp only [LocData.hL, LocData.eL, ite_true]; rfl)
        (fun w' hw' => by simp only [LocData.hL, LocData.eL, ite_true]; rw [Function.update_of_ne hw']; rfl) j
      have h2 := congrFun (hact w hwS hgood k true) j
      have h3 : (d.hL a ha w k true).t w = ctT hab w (d.μ w) (d.ϖ w) k := by
        simp [LocData.hL, hhc]
      rw [h3] at h1
      rw [← h1]
      exact h2
    obtain ⟨B, hB, hBe⟩ := hUS E n π w (σ w) hw (hσ w hwS).1 (by rw [← hKU]; exact (hσ w hwS).2)
    have hev : ∀ k ≤ n, twTr (σ w).ρ (KL n w) (KL n w) (d.hU w k) LinearMap.id = satEig (qV E w) n B k :=
      fun k hk => hBe _ (hϖ w) k hk
    have hR := hRS E hE n a (n - a) hab μ e π s₁ s₂ Pa Pb D (G j) w B (d.ϖ w) hμ hπ hC.g₁ hC.g₂ hC.u₁ hC.u₂ hC.t₁ hC.t₂
      hC.join (hGs j) hj hw hun hB (hϖ w)
    refine ⟨(hR.1 hfix1 fun k hk => ?_).2, fun u hu => (hR.2 u hu ((hCF E a (n - a)).1 w u (G j) hw hu hfix2') fun k hk => ?_).2⟩
    · rw [← hdμ w, ← (hAct E a (n - a) w _ (G j) (hCtk k).1 (hCtk k).2.1).1 hfix1, hP k, hev k hk]
    · rw [← hdμ w, ← (hAct E a (n - a) w _ (G j) (hCtk k).1 (hCtk k).2.1).2 hfix2', hT' k, hev k hk]
  have hfin := ((hCF E a (n - a)).2 Sec hSec).2 (d.T ∪ d.S₀ ∪ d.Bad)
  rw [Filter.eventually_cofinite]
  refine ((d.T ∪ d.S₀ ∪ d.Bad).finite_toSet.union hfin).subset ?_
  intro u hu
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at hu
  obtain ⟨hsu, hnot⟩ := hu
  by_contra hcon
  simp only [Set.mem_union, Finset.mem_coe, Finset.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and] at hcon
  obtain ⟨⟨⟨hT, hS0⟩, hBad⟩, hCX⟩ := hcon
  rcases ((hCF E a (n - a)).2 Sec hSec).1 u hsu with huS | ⟨w, hwS, hw, hwu⟩
  · exact hnot (core u huS hsu hT hS0 hBad).1
  · have hwX : w ∉ d.T ∪ d.S₀ ∪ d.Bad := fun h => hCX w (Finset.mem_union.1 h |>.imp_left Finset.mem_union.1) hwu
    simp only [Finset.mem_union, not_or] at hwX
    exact hnot ((core w hwS hw hwX.1.1 hwX.1.2 hwX.2).2 u hwu)

end PositivityTheory.Rg.BcB.F.FG

end
