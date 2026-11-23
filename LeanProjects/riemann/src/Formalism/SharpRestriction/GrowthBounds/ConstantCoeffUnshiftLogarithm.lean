import Formalism.SharpRestriction.GrowthBounds.MixedCoefficientClosed
import Formalism.LocalToGlobal.CharacterGerms.FirstPartialLawAtPoints

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace SelfConjDifferentials

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem constantCoeff_unshift_logarithm (Y : FBChart C V O dd) (i : Fin dd) : MvPowerSeries.constantCoeff (un1 (Y.lg i)) = 0 := by
  rw [constantCoeff_uncurry, Y.lg_const]

theorem sum_range_list {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Finset.range n, f k = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

theorem exp_sum_range {σ : Type} (f : ℕ → MvPowerSeries σ C) (hf : ∀ k, MvPowerSeries.constantCoeff (f k) = 0)
    (n : ℕ) : mvExp (∑ k ∈ Finset.range n, f k) = ((List.range n).map fun k => mvExp (f k)).prod := by
  induction n with
  | zero => simp [rtj_mvExp_zero]
  | succ n ih =>
    have h0 : MvPowerSeries.constantCoeff (∑ k ∈ Finset.range n, f k) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun k _ => hf k
    rw [Finset.sum_range_succ, VP.exp_add h0 (hf n), ih, List.range_succ, List.map_append, List.prod_append]
    simp

theorem lg_zero (Y : FBChart C V O dd) {τ : Type} (i : Fin dd) :
    MvPowerSeries.subst (fun _ : Fin dd => (0 : MvPowerSeries τ C)) (un1 (Y.lg i)) = 0 := by
  show MvPowerSeries.subst (0 : Fin dd → MvPowerSeries τ C) (un1 (Y.lg i)) = 0
  rw [MvPowerSeries.subst_zero_eq_C_constantCoeff, constantCoeff_unshift_logarithm]
  simp

theorem subst_add_logarithm_additive (Y : FBChart C V O dd) {τ : Type} (a b : Fin dd → MvPowerSeries τ C)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0)
    (i : Fin dd) :
    MvPowerSeries.subst (VP.addAt Y a b) (un1 (Y.lg i)) =
      MvPowerSeries.subst a (un1 (Y.lg i)) + MvPowerSeries.subst b (un1 (Y.lg i)) := by
  have h := lg_addOf Y ![a, b] (fun k j => by fin_cases k; exacts [ha j, hb j]) i
  have e : (fun q : Fin 2 × Fin dd => (![a, b] : Fin 2 → Fin dd → MvPowerSeries τ C) q.1 q.2) = VP.P2 a b := by
    funext q
    obtain ⟨k, j⟩ := q
    fin_cases k <;> simp [VP.P2]
  rw [e] at h
  exact h

theorem lg_sumL (Y : FBChart C V O dd) {τ : Type} (i : Fin dd) :
    ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, VP.GoodPt V a) →
      MvPowerSeries.subst (VP.sumL Y l) (un1 (Y.lg i)) = (l.map fun a => MvPowerSeries.subst a (un1 (Y.lg i))).sum
  | [], _ => by
    show MvPowerSeries.subst (fun _ : Fin dd => (0 : MvPowerSeries τ C)) (un1 (Y.lg i)) = _
    rw [lg_zero, List.map_nil, List.sum_nil]
  | a :: l, h => by
    have ha := h a List.mem_cons_self
    have hl : ∀ b ∈ l, VP.GoodPt V b := fun b hb => h b (List.mem_cons_of_mem _ hb)
    show MvPowerSeries.subst (VP.addAt Y a (VP.sumL Y l)) (un1 (Y.lg i)) = _
    rw [subst_add_logarithm_additive Y a _ ha.1 (VP.good_sumL Y l hl).1, lg_sumL Y i l hl, List.map_cons, List.sum_cons]

theorem pt_eq_of_lg (Y : FBChart C V O dd) {τ : Type} {A B : Fin dd → MvPowerSeries τ C}
    (hA : ∀ j, MvPowerSeries.constantCoeff (A j) = 0) (hB : ∀ j, MvPowerSeries.constantCoeff (B j) = 0)
    (h : ∀ i, MvPowerSeries.subst A (un1 (Y.lg i)) = MvPowerSeries.subst B (un1 (Y.lg i))) : A = B := by
  have hL : MvPowerSeries.HasSubst (fun j => un1 (Y.lg j)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => constantCoeff_unshift_logarithm Y j
  have key : ∀ A : Fin dd → MvPowerSeries τ C, (∀ j, MvPowerSeries.constantCoeff (A j) = 0) → ∀ i,
      MvPowerSeries.subst (fun j => MvPowerSeries.subst A (un1 (Y.lg j))) (un1 (Y.ex i)) = A i := by
    intro A hA i
    have hA' := MvPowerSeries.hasSubst_of_constantCoeff_zero hA
    have hx : un1 (comp1 Y.ex Y.lg i) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
      rw [Y.ex_lg]; exact uncurry_X i
    rw [← MvPowerSeries.subst_comp_subst_apply hL hA', uncurry_comp Y.lg_const, hx, MvPowerSeries.subst_X hA']
  funext i
  rw [← key A hA i, ← key B hB i]
  simp only [h]

theorem hAt_self (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0) {τ : Type}
    (a b : Fin 2 × Fin dd → MvPowerSeries τ C) (ha : ∀ x, MvPowerSeries.constantCoeff (a x) = 0)
    (hb : ∀ x, MvPowerSeries.constantCoeff (b x) = 0) :
    SelfConjCharts.hAt (Y.rawSelf p) a b = ∑ col : Fin 2, VP.hAt Y (fun x => a (col, x)) (fun x => b (col, x)) := by
  have hP : MvPowerSeries.HasSubst (SelfConjCharts.pairSubst a b) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by
      unfold SelfConjCharts.pairSubst
      split_ifs
      exacts [ha _, hb _]
  have hc : ∀ col : Fin 2, MvPowerSeries.subst (SelfConjCharts.pairSubst a b) (hCol col Y.h) =
      VP.hAt Y (fun x => a (col, x)) (fun x => b (col, x)) := by
    intro col
    have hI : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd =>
        (MvPowerSeries.X (q.1, (col, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
    unfold hCol
    rw [MvPowerSeries.subst_comp_subst_apply hI hP]
    show _ = MvPowerSeries.subst (VP.P2 _ _) Y.h
    congr 1
    funext q
    rw [MvPowerSeries.subst_X hP]
    rfl
  show MvPowerSeries.subst (SelfConjCharts.pairSubst a b) (∑ col, hCol col Y.h) = _
  rw [Fin.sum_univ_two, Fin.sum_univ_two, MvPowerSeries.subst_add hP, hc 0, hc 1]

theorem col_left (Y : FBChart C V O dd) {τ : Type} (n : ℕ) (a : ℕ → Fin dd → MvPowerSeries τ C)
    {s c : Fin dd → MvPowerSeries τ C} (ha : ∀ k, VP.GoodPt V (a k)) (hs : VP.GoodPt V s) (hc : VP.GoodPt V c)
    (hsum : s = VP.sumL Y ((List.range n).map a)) :
    IntS V (mvExp (∑ k ∈ Finset.range n, VP.hAt Y (a k) c - VP.hAt Y s c)) ∧
      MvPowerSeries.constantCoeff (∑ k ∈ Finset.range n, VP.hAt Y (a k) c - VP.hAt Y s c) = 0 := by
  obtain ⟨U, hU, e⟩ := VP.biadd_left Y hc ((List.range n).map a) (by
    intro b hb
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hb
    exact ha k)
  rw [← hsum, List.map_map] at e
  have c1 : ∀ k, MvPowerSeries.constantCoeff (VP.hAt Y (a k) c) = 0 := fun k => VP.cc_hAt Y (ha k).1 hc.1
  have c2 : MvPowerSeries.constantCoeff (VP.hAt Y s c) = 0 := VP.cc_hAt Y hs.1 hc.1
  have cS : MvPowerSeries.constantCoeff (∑ k ∈ Finset.range n, VP.hAt Y (a k) c) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun k _ => c1 k
  have c2' : MvPowerSeries.constantCoeff (-VP.hAt Y s c) = 0 := by rw [map_neg, c2, neg_zero]
  have hU' : mvExp (∑ k ∈ Finset.range n, VP.hAt Y (a k) c) = mvExp (VP.hAt Y s c) * U := by
    rw [exp_sum_range (fun k => VP.hAt Y (a k) c) c1 n, e]
    rfl
  have inv : mvExp (VP.hAt Y s c) * mvExp (-VP.hAt Y s c) = 1 := by
    rw [← VP.exp_add c2 c2', add_neg_cancel, rtj_mvExp_zero]
  have key : mvExp (∑ k ∈ Finset.range n, VP.hAt Y (a k) c - VP.hAt Y s c) = U := by
    rw [sub_eq_add_neg, VP.exp_add cS c2', hU', mul_comm (mvExp (VP.hAt Y s c)) U, mul_assoc, inv, mul_one]
  refine ⟨?_, by rw [map_sub, cS, c2, sub_zero]⟩
  rw [key]
  exact hU.1

theorem col_right (Y : FBChart C V O dd) {τ : Type} (n : ℕ) (a : ℕ → Fin dd → MvPowerSeries τ C)
    {s c : Fin dd → MvPowerSeries τ C} (ha : ∀ k, VP.GoodPt V (a k)) (hs : VP.GoodPt V s) (hc : VP.GoodPt V c)
    (hsum : s = VP.sumL Y ((List.range n).map a)) :
    IntS V (mvExp (∑ k ∈ Finset.range n, VP.hAt Y c (a k) - VP.hAt Y c s)) ∧
      MvPowerSeries.constantCoeff (∑ k ∈ Finset.range n, VP.hAt Y c (a k) - VP.hAt Y c s) = 0 := by
  obtain ⟨U, hU, e⟩ := VP.biadd_right Y hc ((List.range n).map a) (by
    intro b hb
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hb
    exact ha k)
  rw [← hsum, List.map_map] at e
  have c1 : ∀ k, MvPowerSeries.constantCoeff (VP.hAt Y c (a k)) = 0 := fun k => VP.cc_hAt Y hc.1 (ha k).1
  have c2 : MvPowerSeries.constantCoeff (VP.hAt Y c s) = 0 := VP.cc_hAt Y hc.1 hs.1
  have cS : MvPowerSeries.constantCoeff (∑ k ∈ Finset.range n, VP.hAt Y c (a k)) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun k _ => c1 k
  have c2' : MvPowerSeries.constantCoeff (-VP.hAt Y c s) = 0 := by rw [map_neg, c2, neg_zero]
  have hU' : mvExp (∑ k ∈ Finset.range n, VP.hAt Y c (a k)) = mvExp (VP.hAt Y c s) * U := by
    rw [exp_sum_range (fun k => VP.hAt Y c (a k)) c1 n, e]
    rfl
  have inv : mvExp (VP.hAt Y c s) * mvExp (-VP.hAt Y c s) = 1 := by
    rw [← VP.exp_add c2 c2', add_neg_cancel, rtj_mvExp_zero]
  have key : mvExp (∑ k ∈ Finset.range n, VP.hAt Y c (a k) - VP.hAt Y c s) = U := by
    rw [sub_eq_add_neg, VP.exp_add cS c2', hU', mul_comm (mvExp (VP.hAt Y c s)) U, mul_assoc, inv, mul_one]
  refine ⟨?_, by rw [map_sub, cS, c2, sub_zero]⟩
  rw [key]
  exact hU.1

theorem biInt_self (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0) :
    SelfConjCharts.BiInt (Y.rawSelf p) V := by
  intro τ _ n a s c ha hs hc hlg
  have gp : ∀ {b : Fin 2 × Fin dd → MvPowerSeries τ C}, SelfConjCharts.IsPt V b → ∀ col : Fin 2,
      VP.GoodPt V (fun x => b (col, x)) :=
    fun hb col => ⟨fun x => (hb (col, x)).1, fun x => (hb (col, x)).2⟩
  have cc0 : ∀ {b : Fin 2 × Fin dd → MvPowerSeries τ C}, SelfConjCharts.IsPt V b → ∀ q,
      MvPowerSeries.constantCoeff (b q) = 0 :=
    fun hb q => (hb q).1
  have hsum : ∀ col : Fin 2,
      (fun x => s (col, x)) = VP.sumL Y ((List.range n).map fun k x => a k (col, x)) := by
    intro col
    have hl : ∀ b ∈ (List.range n).map (fun k x => a k (col, x)), VP.GoodPt V b := by
      intro b hb
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hb
      exact gp (ha k) col
    apply pt_eq_of_lg Y (gp hs col).1 (VP.good_sumL Y _ hl).1
    intro i
    rw [lg_sumL Y i _ hl, List.map_map]
    have h := hlg (col, i)
    change MvPowerSeries.subst s (inCol col (un1 (Y.lg i))) =
      ∑ k ∈ Finset.range n, MvPowerSeries.subst (a k) (inCol col (un1 (Y.lg i))) at h
    have h2 : ∀ k, MvPowerSeries.subst (a k) (inCol col (un1 (Y.lg i))) =
        MvPowerSeries.subst (fun x => a k (col, x)) (un1 (Y.lg i)) :=
      fun k => subst_inCol (cc0 (ha k)) col _
    rw [subst_inCol (cc0 hs)] at h
    simp only [h2] at h
    rw [h, sum_range_list]
    rfl
  constructor
  · have e : ∑ k ∈ Finset.range n, SelfConjCharts.hAt (Y.rawSelf p) (a k) c - SelfConjCharts.hAt (Y.rawSelf p) s c =
        ∑ col : Fin 2, (∑ k ∈ Finset.range n, VP.hAt Y (fun x => a k (col, x)) (fun x => c (col, x)) -
          VP.hAt Y (fun x => s (col, x)) (fun x => c (col, x))) := by
      rw [Finset.sum_congr rfl fun k _ => hAt_self Y p (a k) c (cc0 (ha k)) (cc0 hc),
        hAt_self Y p s c (cc0 hs) (cc0 hc), Finset.sum_comm, ← Finset.sum_sub_distrib]
    have h0 := col_left Y n (fun k x => a k (0, x)) (fun k => gp (ha k) 0) (gp hs 0) (gp hc 0) (hsum 0)
    have h1 := col_left Y n (fun k x => a k (1, x)) (fun k => gp (ha k) 1) (gp hs 1) (gp hc 1) (hsum 1)
    rw [e, Fin.sum_univ_two, VP.exp_add h0.2 h1.2]
    exact h0.1.mul h1.1
  · have e : ∑ k ∈ Finset.range n, SelfConjCharts.hAt (Y.rawSelf p) c (a k) - SelfConjCharts.hAt (Y.rawSelf p) c s =
        ∑ col : Fin 2, (∑ k ∈ Finset.range n, VP.hAt Y (fun x => c (col, x)) (fun x => a k (col, x)) -
          VP.hAt Y (fun x => c (col, x)) (fun x => s (col, x))) := by
      rw [Finset.sum_congr rfl fun k _ => hAt_self Y p c (a k) (cc0 hc) (cc0 (ha k)),
        hAt_self Y p c s (cc0 hc) (cc0 hs), Finset.sum_comm, ← Finset.sum_sub_distrib]
    have h0 := col_right Y n (fun k x => a k (0, x)) (fun k => gp (ha k) 0) (gp hs 0) (gp hc 0) (hsum 0)
    have h1 := col_right Y n (fun k x => a k (1, x)) (fun k => gp (ha k) 1) (gp hs 1) (gp hc 1) (hsum 1)
    rw [e, Fin.sum_univ_two, VP.exp_add h0.2 h1.2]
    exact h0.1.mul h1.1

end SelfConjDifferentials

theorem biadditive_on_columns : BiadditiveOnColumns := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p
  exact SelfConjDifferentials.biInt_self Y p

end Formalism.L2.FormalSeriesBounds
