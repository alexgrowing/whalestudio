import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.WordIdAt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.DoubleSumFinprodFactor

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace PositivityTheory.Rg.BcB.F.B3

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PLocWord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (d : LocData E n)

def HG (a : ℕ) (L : LM d.kap a (n - a)) : Prop :=
  (∀ w ∈ d.P, ∀ x y, IsHecke (d.lev a w) (L.m w x y)) ∧ (∀ w ∉ d.P, IsHecke (d.lev a w) (L.s w)) ∧
    ∀ w, IsHecke (d.lev₂ a w) (L.t w)

theorem levOk (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev a w : Set (GLw a w × GLw (n - a) w)) ∧ d.lev a w ≤ K2 a (n - a) w := by
  by_cases hP : w ∈ d.P
  · exact LocComm.lev_ok d hd ha hP
  · have hT : w ∉ d.T := fun h => hP (Finset.mem_union_left _ h)
    by_cases hSB : w ∈ d.S₀ ∪ d.Bad
    · rw [PSeen.lev_eq d hd hSB]
      exact PSeen.L_ok d hd ha hSB
    · simp only [LocData.lev, if_neg hT, if_neg hSB]
      exact ⟨LocComm.isOpen_levelSubgroup' _ _ _, le_rfl⟩

def idA (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) := idemAlg E a (n - a) w _ (levOk d hd ha w).1 (levOk d hd ha w).2

def idB (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) :=
  idemAlg E a (n - a) w _ (PSeen.lev₂_ok d hd ha w).1 (PSeen.lev₂_ok d hd ha w).2

theorem diagH {a : ℕ} {w : Pl E} {K : Subgroup (GLw a w × GLw (n - a) w)} {f : LF a (n - a) w} (hf : IsHecke K f)
    (x y : d.kap w) : IsHecke K (d.diag (fun _ => f) x y) := by
  unfold LocData.diag
  split_ifs
  · exact hf
  · exact LocComm.isHecke_zero _

theorem hgEL (hd : d.Ok) {a : ℕ} (ha : a ≤ n) : HG d a (d.eL a) :=
  ⟨fun w _ x y => diagH d (idA d hd ha w).1 x y, fun w _ => (idA d hd ha w).1, fun w => (idB d hd ha w).1⟩

theorem hg_mul {a : ℕ} {L L' : LM d.kap a (n - a)} (h : HG d a L) (h' : HG d a L') : HG d a (L.mul L') := by
  refine ⟨fun w hw x y => ?_, fun w hw => ?_, fun w => ?_⟩
  · show IsHecke _ (∑ z, mconv (L.m w x z) (L'.m w z y))
    exact PSeen.isHecke_fsum _ Finset.univ (fun z => mconv (L.m w x z) (L'.m w z y))
      fun z _ => PSeen.mconv_hecke _ (h.1 w hw x z) (h'.1 w hw z y)
  · exact PSeen.mconv_hecke _ (h.2.1 w hw) (h'.2.1 w hw)
  · exact PSeen.mconv_hecke _ (h.2.2 w) (h'.2.2 w)

theorem hg_adj (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {L : LM d.kap a (n - a)} (h : HG d a L) : HG d a L.adj :=
  ⟨fun w hw x y => ((idA d hd ha w).2.2 _ (h.1 w hw y x)).2.2, fun w hw => ((idA d hd ha w).2.2 _ (h.2.1 w hw)).2.2,
    fun w => ((idB d hd ha w).2.2 _ (h.2.2 w)).2.2⟩

theorem hgBeta (hd : d.Ok) {a : ℕ} (ha : a ≤ n) : HG d a (d.betaL a ha) :=
  ⟨fun w hw x y => LocComm.hecke_beta d (PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 E) hd ha hw x y, fun w _ => (idA d hd ha w).1,
    fun w => (idB d hd ha w).1⟩

theorem hgGen (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {L : LM d.kap a (n - a)} (hL : d.IsGen a ha L) : HG d a L := by
  refine ⟨fun w hw x y => ?_, fun w _ => ?_, fun w => ?_⟩
  · rw [LocComm.gen_m d hL]
    exact (hgEL d hd ha).1 w hw x y
  · rcases LocComm.generator_first_levi_position d hL w with h | ⟨hg, k, h⟩
    · rw [h]; exact (idA d hd ha w).1
    · rw [h, LocComm.lev_good d hg]; exact LocComm.hecke_hc d hd ha hg k
  · rcases LocComm.generator_second_levi_position d hL w with h | ⟨hg, k, h⟩
    · rw [h]; exact (idB d hd ha w).1
    · rw [h, LocComm.lev₂_good d hg]; exact LocComm.hecke_hc d hd ha hg k

theorem unit_eqv (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {X : LM d.kap a (n - a)} (h : HG d a X) :
    ((d.eL a).mul X).Eqv d.P X ∧ (X.mul (d.eL a)).Eqv d.P X := by
  refine ⟨⟨fun w hw => ?_, fun w hw => ?_, ?_⟩, ⟨fun w hw => ?_, fun w hw => ?_, ?_⟩⟩
  · funext x y
    show ∑ z, mconv (d.diag (fun _ => idem (d.lev a w)) x z) (X.m w z y) = X.m w x y
    rw [LocComm.sum_diag_left]
    exact ((idA d hd ha w).2.2 _ (h.1 w hw x y)).1
  · exact ((idA d hd ha w).2.2 _ (h.2.1 w hw)).1
  · funext w
    exact ((idB d hd ha w).2.2 _ (h.2.2 w)).1
  · funext x y
    show ∑ z, mconv (X.m w x z) (d.diag (fun _ => idem (d.lev a w)) z y) = X.m w x y
    rw [LocComm.sum_diag_right]
    exact ((idA d hd ha w).2.2 _ (h.1 w hw x y)).2.1
  · exact ((idA d hd ha w).2.2 _ (h.2.1 w hw)).2.1
  · funext w
    exact ((idB d hd ha w).2.2 _ (h.2.2 w)).2.1

theorem ok_adj {a : ℕ} {L : LM d.kap a (n - a)} (h : L.Ok d.P) : L.adj.Ok d.P := by
  refine ⟨fun x y => ?_, Fm.isTestFunction_star h.2⟩
  rw [Fm.adj_ent]
  exact Fm.isTestFunction_star (h.1 y x)

theorem kinds {a : ℕ} (ha : a ≤ n) (p : LL d) : locL d a ha p = d.betaL a ha ∨ d.IsGen a ha (locL d a ha p) ∨
    ∃ L, d.IsGen a ha L ∧ locL d a ha p = L.adj := by
  rcases p with u | u | ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (Or.inl rfl))
  · have hG : d.IsGen a ha (d.hL a ha w' k intersection_update_fsHerm_neg_one) := Or.inr ⟨w', k, intersection_update_fsHerm_neg_one, hg, rfl⟩
    cases st
    · exact Or.inr (Or.inl (by simpa [locL] using hG))
    · exact Or.inr (Or.inr ⟨_, hG, by simp [locL]⟩)

theorem hgL (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (p : LL d) : HG d a (locL d a ha p) := by
  rcases kinds d ha p with h | h | ⟨L, hL, h⟩
  · rw [h]; exact hgBeta d hd ha
  · exact hgGen d hd ha h
  · rw [h]; exact hg_adj d hd ha (hgGen d hd ha hL)

theorem hg_foldr (hd : d.Ok) {a : ℕ} (ha : a ≤ n) : ∀ ls : List (LL d), HG d a ((ls.map (locL d a ha)).foldr LM.mul (d.eL a))
  | [] => hgEL d hd ha
  | p :: ls => hg_mul d (hgL d hd ha p) (hg_foldr hd ha ls)

def AtW {a : ℕ} (w : Pl E) (L L' : LM d.kap a (n - a)) : Prop :=
  (w ∈ d.P → L.m w = L'.m w) ∧ (w ∉ d.P → L.s w = L'.s w)

theorem atW_refl {a : ℕ} (w : Pl E) (L : LM d.kap a (n - a)) : AtW d w L L := ⟨fun _ => rfl, fun _ => rfl⟩

theorem atW_trans {a : ℕ} {w : Pl E} {L₁ L₂ L₃ : LM d.kap a (n - a)} (h : AtW d w L₁ L₂) (h' : AtW d w L₂ L₃) :
    AtW d w L₁ L₃ := ⟨fun hw => (h.1 hw).trans (h'.1 hw), fun hw => (h.2 hw).trans (h'.2 hw)⟩

theorem atW_of_eqv {a : ℕ} {w : Pl E} {L L' : LM d.kap a (n - a)} (h : L.Eqv d.P L') : AtW d w L L' :=
  ⟨fun hw => h.1 w hw, fun hw => h.2.1 w hw⟩

theorem atW_mul {a : ℕ} {w : Pl E} {A A' B B' : LM d.kap a (n - a)} (h : AtW d w A A') (h' : AtW d w B B') :
    AtW d w (A.mul B) (A'.mul B') := by
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · show (fun x y => ∑ z, mconv (A.m w x z) (B.m w z y)) = fun x y => ∑ z, mconv (A'.m w x z) (B'.m w z y)
    rw [h.1 hw, h'.1 hw]
  · show mconv (A.s w) (B.s w) = mconv (A'.s w) (B'.s w)
    rw [h.2 hw, h'.2 hw]

theorem atW_tr {a : ℕ} {w : Pl E} {L L' : LM d.kap a (n - a)} (h : AtW d w L L') (N : ∀ w, d.kap w → d.kap w → ℂ) :
    L.tr d.P N w = L'.tr d.P N w := by
  unfold LM.tr
  split_ifs with hw
  · rw [h.1 hw]
  · exact h.2 hw

theorem genAtW {a : ℕ} {ha : a ≤ n} {w : Pl E} (hw : w ∈ d.B) {L : LM d.kap a (n - a)} (hL : d.IsGen a ha L) :
    AtW d w L (d.eL a) ∧ AtW d w L.adj (d.eL a) := by
  have hs : L.s w = idem (d.lev a w) := by
    rcases LocComm.generator_first_levi_position d hL w with h | ⟨h, -⟩
    · exact h
    · exact absurd h (PSeen.notGood d hw)
  refine ⟨⟨fun _ => by rw [LocComm.gen_m d hL], fun _ => hs⟩, ⟨fun _ => by rw [LocComm.adj_m d hL], fun _ => ?_⟩⟩
  show lfStar (L.s w) = idem (d.lev a w)
  rw [hs, LocComm.lfStar_idem]

def cw (a : ℕ) (ha : a ≤ n) : ℕ → LM d.kap a (n - a)
  | 0 => d.eL a
  | j + 1 => MLM.pw (d.betaL a ha) j

theorem beta_cw (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) :
    ∀ c, AtW d w ((d.betaL a ha).mul (cw d a ha c)) (cw d a ha (c + 1))
  | 0 => atW_of_eqv d (unit_eqv d hd ha (hgBeta d hd ha)).2
  | _ + 1 => atW_refl d w _

theorem prodW (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hw : w ∈ d.B) : ∀ ls : List (LL d),
    AtW d w ((ls.map (locL d a ha)).foldr LM.mul (d.eL a)) (cw d a ha (ls.countP Sum.isLeft))
  | [] => by
    rw [List.countP_nil]
    exact atW_refl d w _
  | p :: ls => by
    have ih := prodW hd ha hw ls
    have hX := hg_foldr d hd ha ls
    have nb : ∀ L : LM d.kap a (n - a), AtW d w L (d.eL a) →
        AtW d w (L.mul ((ls.map (locL d a ha)).foldr LM.mul (d.eL a))) (cw d a ha (ls.countP Sum.isLeft)) :=
      fun L hL => atW_trans d (atW_trans d (atW_mul d hL (atW_refl d w _)) (atW_of_eqv d (unit_eqv d hd ha hX).1)) ih
    rcases p with u | u | ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩
    · have hc : (Sum.inl u :: ls : List (LL d)).countP Sum.isLeft = ls.countP Sum.isLeft + 1 := by
        simp [List.countP_cons]
      rw [hc]
      exact atW_trans d (atW_mul d (atW_refl d w (d.betaL a ha)) ih) (beta_cw d hd ha w _)
    · have hc : (Sum.inr (Sum.inl u) :: ls : List (LL d)).countP Sum.isLeft = ls.countP Sum.isLeft := by
        simp [List.countP_cons]
      rw [hc]
      exact nb _ (atW_refl d w _)
    · have hc : (Sum.inr (Sum.inr ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩) :: ls : List (LL d)).countP Sum.isLeft =
          ls.countP Sum.isLeft := by
        simp [List.countP_cons]
      rw [hc]
      have hG : d.IsGen a ha (d.hL a ha w' k intersection_update_fsHerm_neg_one) := Or.inr ⟨w', k, intersection_update_fsHerm_neg_one, hg, rfl⟩
      cases st
      · exact nb _ (genAtW d hw hG).1
      · exact nb _ (genAtW d hw hG).2

theorem offStep (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hP : w ∉ d.P) {l X : LM d.kap a (n - a)} (hX : HG d a X)
    (hs : l.s w = idem (d.lev a w)) (ht : l.t w = idem (d.lev₂ a w)) :
    (l.mul X).s w = X.s w ∧ (l.mul X).t w = X.t w := by
  refine ⟨?_, ?_⟩
  · show mconv (l.s w) (X.s w) = X.s w
    rw [hs]
    exact ((idA d hd ha w).2.2 _ (hX.2.1 w hP)).1
  · show mconv (l.t w) (X.t w) = X.t w
    rw [ht]
    exact ((idB d hd ha w).2.2 _ (hX.2.2 w)).1

theorem hL_off {a : ℕ} (ha : a ≤ n) {w w' : Pl E} (hne : w ≠ w') (k : ℕ) (intersection_update_fsHerm_neg_one : Bool) :
    (d.hL a ha w' k intersection_update_fsHerm_neg_one).s w = idem (d.lev a w) ∧ (d.hL a ha w' k intersection_update_fsHerm_neg_one).t w = idem (d.lev₂ a w) := by
  cases intersection_update_fsHerm_neg_one <;> simp [LocData.hL, Function.update_of_ne hne, LocData.eL]

theorem offB (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hP : w ∉ d.P) : ∀ ls : List (LL d),
    ((ls.map (locL d a ha)).foldr LM.mul (d.eL a)).s w = (MLM.wordLS d a ha w (atPlace d w ls)).s w ∧
    ((ls.map (locL d a ha)).foldr LM.mul (d.eL a)).t w = (MLM.wordLS d a ha w (atPlace d w ls)).t w
  | [] => ⟨rfl, rfl⟩
  | p :: ls => by
    obtain ⟨ih1, ih2⟩ := offB hd ha hP ls
    have hX := hg_foldr d hd ha ls
    have fin : ∀ l : LM d.kap a (n - a), l.s w = idem (d.lev a w) → l.t w = idem (d.lev₂ a w) →
        (l.mul ((ls.map (locL d a ha)).foldr LM.mul (d.eL a))).s w = (MLM.wordLS d a ha w (atPlace d w ls)).s w ∧
        (l.mul ((ls.map (locL d a ha)).foldr LM.mul (d.eL a))).t w = (MLM.wordLS d a ha w (atPlace d w ls)).t w := by
      intro l hs ht
      obtain ⟨e1, e2⟩ := offStep d hd ha hP hX hs ht
      exact ⟨e1.trans ih1, e2.trans ih2⟩
    rcases p with u | u | ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩
    · have e : atPlace d w (Sum.inl u :: ls) = atPlace d w ls := by simp [atPlace]
      rw [e]
      exact fin _ rfl rfl
    · have e : atPlace d w (Sum.inr (Sum.inl u) :: ls) = atPlace d w ls := by simp [atPlace]
      rw [e]
      exact fin _ rfl rfl
    · by_cases hw : w' = w
      · subst hw
        have e : atPlace d w' (Sum.inr (Sum.inr ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩) :: ls) = (k, intersection_update_fsHerm_neg_one, st) :: atPlace d w' ls := by
          simp [atPlace]
        rw [e]
        refine ⟨?_, ?_⟩
        · show mconv ((locL d a ha (Sum.inr (Sum.inr ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩))).s w')
              (((ls.map (locL d a ha)).foldr LM.mul (d.eL a)).s w') =
            mconv ((if st then (d.hL a ha w' k intersection_update_fsHerm_neg_one).adj else d.hL a ha w' k intersection_update_fsHerm_neg_one).s w')
              ((MLM.wordLS d a ha w' (atPlace d w' ls)).s w')
          rw [ih1]
          rfl
        · show mconv ((locL d a ha (Sum.inr (Sum.inr ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩))).t w')
              (((ls.map (locL d a ha)).foldr LM.mul (d.eL a)).t w') =
            mconv ((if st then (d.hL a ha w' k intersection_update_fsHerm_neg_one).adj else d.hL a ha w' k intersection_update_fsHerm_neg_one).t w')
              ((MLM.wordLS d a ha w' (atPlace d w' ls)).t w')
          rw [ih2]
          rfl
      · have e : atPlace d w (Sum.inr (Sum.inr ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩) :: ls) = atPlace d w ls := by
          simp [atPlace, hw]
        rw [e]
        obtain ⟨hs, ht⟩ := hL_off d ha (Ne.symm hw) k intersection_update_fsHerm_neg_one
        cases st
        · exact fin _ hs ht
        · refine fin _ ?_ ?_
          · show lfStar ((d.hL a ha w' k intersection_update_fsHerm_neg_one).s w) = _
            rw [hs, LocComm.lfStar_idem]
          · show lfStar ((d.hL a ha w' k intersection_update_fsHerm_neg_one).t w) = _
            rw [ht, LocComm.lfStar_idem]

theorem atPlace_nil {w : Pl E} (hw : ¬ d.Good w) : ∀ ls : List (LL d), atPlace d w ls = []
  | [] => rfl
  | p :: ls => by
    have ih := atPlace_nil hw ls
    rcases p with u | u | ⟨⟨w', hg⟩, x⟩
    · simpa [atPlace] using ih
    · simpa [atPlace] using ih
    · have hne : w' ≠ w := fun e => hw (e ▸ hg)
      simpa [atPlace, hne] using ih

end PLocWord

open PLocWord in
theorem locWord : LocWord := by
  intro E _ _ _ n d hd a ha ls N hN
  have hP : ∀ w, w ∉ d.B → w ∉ d.P := fun w hw h => hw (by
    simp only [LocData.B, LocData.P, Finset.mem_union] at h ⊢
    tauto)
  have hprod : prodL d ls a = (d.fixL a).mul ((ls.map (locL d a ha)).foldr LM.mul (d.eL a)) := by
    rw [prodL, dif_pos ha]
    rfl
  refine ⟨fun p => ⟨?_, (unit_eqv d hd ha (hgL d hd ha p)).1, ?_⟩, fun w hw => ?_, fun w hw => ?_,
    fun w hw => atPlace_nil d hw ls⟩
  · have hOk := BlockFiniteConvolution.locOk₀ E n d hd a ha
    rcases kinds d ha p with h | h | ⟨L, hL, h⟩
    · rw [h]; exact hOk.2.1
    · exact hOk.2.2.2 _ h
    · rw [h]; exact ok_adj d (hOk.2.2.2 _ hL)
  · rcases kinds d ha p with h | h | ⟨L, hL, h⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨L, hL, h⟩)
  · rw [hprod]
    have h1 := atW_mul d (atW_refl d w (d.fixL a)) (prodW d hd ha hw ls)
    rw [hN] at h1
    exact atW_tr d h1 d.one
  · have hwP := hP w hw
    have hBad : w ∉ d.Bad := fun h => hw (by simp [LocData.B, h])
    obtain ⟨e1, e2⟩ := offB d hd ha hwP ls
    have hs : (d.fixL a).s w = idem (d.lev a w) := by simp [LocData.fixL, hBad]
    obtain ⟨f1, f2⟩ := offStep d hd ha hwP (hg_foldr d hd ha ls) hs rfl
    rw [hprod]
    exact ⟨f1.trans e1, f2.trans e2⟩

end PositivityTheory.Rg.BcB.F.B3

end
