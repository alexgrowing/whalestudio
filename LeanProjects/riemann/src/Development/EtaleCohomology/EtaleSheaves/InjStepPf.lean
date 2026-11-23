import Development.EtaleCohomology.EtaleSheaves.ZarIndPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf LateralTheory.E.ZarIndPf

namespace LateralTheory.E.InjStepPf

def TwoStep : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i n : ℤ,
  (∀ U : S.Opens, IsCompact (U : Set S) → Bij q i (n - 1) f p U) →
  ∀ (U V W : S.Opens) (hV : V ≤ U) (hW : W ≤ U), IsCompact (V : Set S) → IsCompact (W : Set S) →
  ∀ x : Ht q (sch.obj (overO p U)) n i, pull _ (sch.map (fO f p U)) _ _ x = 0 →
  pull _ (sch.map (resO p hV)) _ _ x = 0 → pull _ (sch.map (resO p hW)) _ _ x = 0 →
  pull _ (sch.map (resO p (sup_le hV hW))) _ _ x = 0

def EmptyH : Prop := Hyp → ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (U : S.Opens), (U : Set S) = ∅ →
  ∀ (i n : ℤ) (x : Ht q (sch.obj (overO p U)) n i), x = 0

variable {X S : Scheme.{0}}

theorem resO_comp (p : X ⟶ S) {V W U : S.Opens} (h1 : V ≤ W) (h2 : W ≤ U) :
    resO p h1 ≫ resO p h2 = resO p (h1.trans h2) := by
  apply pullback.hom_ext <;> simp only [resO, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Scheme.homOfLE_homOfLE, Category.comp_id]

theorem resO_refl (p : X ⟶ S) (U : S.Opens) : resO p (le_refl U) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [resO]

theorem dies_mono {q : ℕ} {i n : ℤ} (p : X ⟶ S) {V W U : S.Opens} (h1 : V ≤ W) (h2 : W ≤ U)
    (x : Ht q (sch.obj (overO p U)) n i) (hx : pull _ (sch.map (resO p h2)) _ _ x = 0) :
    pull _ (sch.map (resO p (h1.trans h2))) _ _ x = 0 := by
  rw [← resO_comp p h1 h2, Functor.map_comp, pull_comp, hx, map_zero]

def OverMV : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (i m : ℤ) (V W : S.Opens),
  ∃ (δX : Ht q (sch.obj (overO p (V ⊓ W))) m i →+ Ht q (sch.obj (overO p (V ⊔ W))) (m + 1) i)
    (δY : Ht q (sch.obj (overO (f ≫ p) (V ⊓ W))) m i →+ Ht q (sch.obj (overO (f ≫ p) (V ⊔ W))) (m + 1) i),
  (∀ x, pull _ (sch.map (resO p (le_sup_left : V ≤ V ⊔ W))) _ _ x = 0 →
      pull _ (sch.map (resO p (le_sup_right : W ≤ V ⊔ W))) _ _ x = 0 → ∃ w, δX w = x) ∧
  (∀ a b, δX (pull _ (sch.map (resO p (inf_le_left : V ⊓ W ≤ V))) _ _ a -
      pull _ (sch.map (resO p (inf_le_right : V ⊓ W ≤ W))) _ _ b) = 0) ∧
  (∀ w, δY w = 0 → ∃ a b, w = pull _ (sch.map (resO (f ≫ p) (inf_le_left : V ⊓ W ≤ V))) _ _ a -
      pull _ (sch.map (resO (f ≫ p) (inf_le_right : V ⊓ W ≤ W))) _ _ b) ∧
  ∀ w, δY (pull _ (sch.map (fO f p (V ⊓ W))) _ _ w) = pull _ (sch.map (fO f p (V ⊔ W))) _ _ (δX w)

theorem fO_res {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO (f ≫ p) h ≫ fO f p U = fO f p V ≫ resO p h := by
  apply pullback.hom_ext <;> simp only [resO, fO, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
    pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem pull_fO_res {q : ℕ} {i n : ℤ} {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U)
    (x : Ht q (sch.obj (overO p U)) n i) :
    pull _ (sch.map (fO f p V)) _ _ (pull _ (sch.map (resO p h)) _ _ x) =
      pull _ (sch.map (resO (f ≫ p) h)) _ _ (pull _ (sch.map (fO f p U)) _ _ x) := by
  rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, fO_res]

theorem pull_res_res {q : ℕ} {i n : ℤ} (p : X ⟶ S) {V W U : S.Opens} (h1 : V ≤ W) (h2 : W ≤ U)
    (x : Ht q (sch.obj (overO p U)) n i) :
    pull _ (sch.map (resO p h1)) _ _ (pull _ (sch.map (resO p h2)) _ _ x) = pull _ (sch.map (resO p (h1.trans h2))) _ _ x := by
  rw [← pull_comp, ← Functor.map_comp, resO_comp]

theorem TwoStep_of (hO : OverMV) : TwoStep := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i n hb U V W hV hW hVc hWc x hx hdV hdW
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have hb' : ∀ U : S.Opens, IsCompact (U : Set S) → Bij q i m f p U := by simpa using hb
  obtain ⟨δX, δY, e1, e2, e3, e4⟩ := hO hM hH q f p i m V W
  set x' := pull _ (sch.map (resO p (sup_le hV hW))) _ _ x with hx'
  have d1 : pull _ (sch.map (resO p (le_sup_left : V ≤ V ⊔ W))) _ _ x' = 0 := by
    rw [hx', pull_res_res]; exact hdV
  have d2 : pull _ (sch.map (resO p (le_sup_right : W ≤ V ⊔ W))) _ _ x' = 0 := by
    rw [hx', pull_res_res]; exact hdW
  obtain ⟨w, hw⟩ := e1 x' d1 d2
  have fx' : pull _ (sch.map (fO f p (V ⊔ W))) _ _ x' = 0 := by
    rw [hx', pull_fO_res, hx, map_zero]
  have hδ : δY (pull _ (sch.map (fO f p (V ⊓ W))) _ _ w) = 0 := by rw [e4, hw, fx']
  obtain ⟨a', b', hab⟩ := e3 _ hδ
  obtain ⟨a, rfl⟩ := (hb' V hVc).2 a'
  obtain ⟨b, rfl⟩ := (hb' W hWc).2 b'
  have hI : IsCompact ((V ⊓ W : S.Opens) : Set S) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ V.isOpen hVc W.isOpen hWc
  have hw2 : w = pull _ (sch.map (resO p (inf_le_left : V ⊓ W ≤ V))) _ _ a -
      pull _ (sch.map (resO p (inf_le_right : V ⊓ W ≤ W))) _ _ b := by
    apply (hb' _ hI).1
    rw [hab, map_sub, pull_fO_res, pull_fO_res]
  rw [← hw, hw2, e2]

theorem InjStep_of (hT : TwoStep) (hE : EmptyH) : InjStep := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i n hg hb U hU
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_cases hne : (U : Set S) = ∅
  · exact hE hH q p U hne i n x
  obtain ⟨s0, hs0⟩ := Set.nonempty_iff_ne_empty.2 hne

  have loc : ∀ s ∈ (U : Set S), ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ IsCompact (V : Set S) ∧
      pull _ (sch.map (resO p h)) _ _ x = 0 := by
    intro s hs
    obtain ⟨V, hVU, hsV, hd⟩ := (hg s).1 U hs x hx
    obtain ⟨V', hV'B, hsV', hV'V⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens) hsV
    exact ⟨V', hV'V.trans hVU, hsV', IsAffineOpen.isCompact hV'B, dies_mono p hV'V hVU x hd⟩
  let P : Set S → Prop := fun T => ∃ (V : S.Opens) (h : V ≤ U), T ⊆ V ∧ IsCompact (V : Set S) ∧
      pull _ (sch.map (resO p h)) _ _ x = 0
  have hP : P (U : Set S) := by
    refine hU.induction_on (p := P) ?_ ?_ ?_ ?_
    · obtain ⟨V, h, _, hc, hd⟩ := loc s0 hs0
      exact ⟨V, h, Set.empty_subset _, hc, hd⟩
    · intro s t hst ⟨V, h, htV, hc, hd⟩
      exact ⟨V, h, hst.trans htV, hc, hd⟩
    · intro s t ⟨V, h, hsV, hc, hd⟩ ⟨W, h', htW, hc', hd'⟩
      refine ⟨V ⊔ W, sup_le h h', ?_, ?_, hT hM hH q f p hq i n hb U V W h h' hc hc' x hx hd hd'⟩
      · exact Set.union_subset_union hsV htW
      · simpa using hc.union hc'
    · intro s hs
      obtain ⟨V, h, hsV, hc, hd⟩ := loc s hs
      exact ⟨V, mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds hsV), V, h, subset_rfl, hc, hd⟩
  obtain ⟨V, h, hUV, _, hd⟩ := hP
  have hVU : V = U := le_antisymm h hUV
  subst hVU
  simpa [resO_refl, pull_id] using hd

end LateralTheory.E.InjStepPf
