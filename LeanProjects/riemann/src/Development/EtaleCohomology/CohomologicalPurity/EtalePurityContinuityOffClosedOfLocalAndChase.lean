import Development.EtaleCohomology.CohomologicalPurity.OffContStepPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem pairFiveS_surj (bd : LeafBd) (q : ℕ) {J : Type} [SmallCategory J] [IsFiltered J] (F : Jᵒᵖ ⥤ Arrow Spc)
    (P : Arrow Spc) (c : ∀ j, P ⟶ F.obj (op j)) (hc : ∀ j k (f : j ⟶ k), c k ≫ F.map f.op = c j)
    (hm : ∀ j, Mono (F.obj (op j)).hom) (hP : Mono P.hom) (i : ℤ) (hL : ∀ m, ContL q F P c m i)
    (hR : ∀ m, ContR q F P c m i) (m : ℤ) (x : Hs q P (m + 1) i) :
    ∃ j, ∃ y, Hs.pull q (c j) (m + 1) i y = x := by
  obtain ⟨δ, hex, hnat, -⟩ := bd
  obtain ⟨j, y, hy⟩ := (hR (m + 1)).1 (Hs.fgt q P (m + 1) i x)
  have h0 : pull _ (c j).left (tw q i) (m + 1) (pull _ (F.obj (op j)).hom (tw q i) (m + 1) y) = 0 := by
    rw [← GlobalTheory.EtC.pull_comp, Arrow.w (c j), GlobalTheory.EtC.pull_comp, hy]
    exact ((hex q P hP (m + 1) i).1 _).mpr ⟨x, rfl⟩
  obtain ⟨k, f, hk⟩ := (hL (m + 1)).2 j _ h0
  have hk' : pull _ (F.obj (op k)).hom (tw q i) (m + 1) (pull _ (F.map f.op).right (tw q i) (m + 1) y) = 0 := by
    rw [← GlobalTheory.EtC.pull_comp, ← Arrow.w (F.map f.op), GlobalTheory.EtC.pull_comp, hk]
  obtain ⟨s, hs⟩ := ((hex q _ (hm k) (m + 1) i).1 _).mp hk'
  have hv : Hs.fgt q P (m + 1) i (x - Hs.pull q (c k) _ _ s) = 0 := by
    rw [map_sub, Hs.fgt_pull, hs, ← GlobalTheory.EtC.pull_comp, ← Arrow.comp_right, hc, hy, sub_self]
  obtain ⟨u, hu⟩ := ((hex q P hP m i).2.2 _).mp hv
  obtain ⟨l, a, ha⟩ := (hL m).1 u
  rw [← ha, ← hnat q _ _ (c l) hP (hm l)] at hu
  obtain ⟨M, g1, g2, -⟩ := IsFilteredOrEmpty.cocone_objs k l
  refine ⟨M, Hs.pull q (F.map g1.op) _ _ s + Hs.pull q (F.map g2.op) _ _ (δ q _ m i a), ?_⟩
  rw [map_add, ← Hs.pullComp, ← Hs.pullComp, hc, hc, hu, add_sub_cancel]

theorem pairFiveS_inj (bd : LeafBd) (q : ℕ) {J : Type} [SmallCategory J] [IsFiltered J] (F : Jᵒᵖ ⥤ Arrow Spc)
    (P : Arrow Spc) (c : ∀ j, P ⟶ F.obj (op j)) (hc : ∀ j k (f : j ⟶ k), c k ≫ F.map f.op = c j)
    (hm : ∀ j, Mono (F.obj (op j)).hom) (hP : Mono P.hom) (i : ℤ) (hL : ∀ m, ContL q F P c m i)
    (hR : ∀ m, ContR q F P c m i) (m : ℤ) (j : J) (y : Hs q (F.obj (op j)) (m + 1) i)
    (hy : Hs.pull q (c j) (m + 1) i y = 0) :
    ∃ (k : J) (f : j ⟶ k), Hs.pull q (F.map f.op) (m + 1) i y = 0 := by
  obtain ⟨δ, hex, hnat, -⟩ := bd
  have h0 : pull _ (c j).right (tw q i) (m + 1) (Hs.fgt q _ (m + 1) i y) = 0 := by
    rw [← Hs.fgt_pull, hy, map_zero]
  obtain ⟨k, f, hk⟩ := (hR (m + 1)).2 j _ h0
  rw [← Hs.fgt_pull] at hk
  obtain ⟨a, ha⟩ := ((hex q _ (hm k) m i).2.2 _).mp hk
  have hz : δ q P m i (pull _ (c k).left (tw q i) m a) = 0 := by
    rw [← hnat q _ _ (c k) hP (hm k), ha, ← Hs.pullComp, hc, hy]
  obtain ⟨b, hb⟩ := ((hex q P hP m i).2.1 _).mp hz
  obtain ⟨l, e, he⟩ := (hR m).1 b
  obtain ⟨M, g1, g2, -⟩ := IsFilteredOrEmpty.cocone_objs k l
  have hd : pull _ (c M).left (tw q i) m (pull _ (F.map g1.op).left (tw q i) m a -
      pull _ (F.obj (op M)).hom (tw q i) m (pull _ (F.map g2.op).right (tw q i) m e)) = 0 := by
    rw [map_sub, ← GlobalTheory.EtC.pull_comp, ← Arrow.comp_left, hc, ← hb, ← he, ← GlobalTheory.EtC.pull_comp,
      ← GlobalTheory.EtC.pull_comp, ← GlobalTheory.EtC.pull_comp, Category.assoc, ← Arrow.w (F.map g2.op), ← Category.assoc, ← Arrow.comp_left, hc,
      Arrow.w (c l), sub_self]
  obtain ⟨p, h, hp⟩ := (hL m).2 M _ hd
  rw [map_sub, sub_eq_zero, ← GlobalTheory.EtC.pull_comp, ← Arrow.comp_left, ← F.map_comp, ← op_comp,
    ← GlobalTheory.EtC.pull_comp, Arrow.w (F.map h.op), GlobalTheory.EtC.pull_comp] at hp
  refine ⟨p, f ≫ g1 ≫ h, ?_⟩
  have e1 : F.map (f ≫ g1 ≫ h).op = F.map (g1 ≫ h).op ≫ F.map f.op := by rw [op_comp, F.map_comp]
  rw [e1, Hs.pullComp, ← ha, hnat q _ _ _ (hm p) (hm k), hp]
  exact ((hex q _ (hm p) m i).2.1 _).mpr ⟨_, rfl⟩

theorem pairFiveS : PairFiveS := by
  intro bd q J _ _ F P c hc hm hP i hL hR n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  exact ⟨pairFiveS_surj bd q F P c hc hm hP i hL hR m,
    fun j y hy => pairFiveS_inj bd q F P c hc hm hP i hL hR m j y hy⟩

theorem etale_purity_continuity_off_closed_of_local_and_chase (hL : OffContLoc) (hG : OffChaseGeo) : OffContStep :=
  etale_complement_continuity_induction_of_localization_and_pair_lemmas hL pairFiveS hG

end LateralTheory.CohomologicalPurity
