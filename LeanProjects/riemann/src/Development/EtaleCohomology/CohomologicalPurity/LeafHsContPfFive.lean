import Development.EtaleCohomology.CohomologicalPurity.LeafHsContPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem opnMap_tri {X'' X' X : Scheme.{0}} {g : X'' ⟶ X} (a : X'' ⟶ X') (b : X' ⟶ X) (e : g = a ≫ b)
    (U'' : X''.Opens) (U' : X'.Opens) (U : X.Opens) (h : U'' ≤ g ⁻¹ᵁ U) (h1 : U'' ≤ a ⁻¹ᵁ U') (h2 : U' ≤ b ⁻¹ᵁ U) :
    opnMap g U'' U h = opnMap a U'' U' h1 ≫ opnMap b U' U h2 := by
  subst e; exact opnMap_comp _ _ _ _ _ h1 h2 h

theorem fgt_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.fgt q P' n i (Hs.pull q φ n i x) = pull _ φ.right (tw q i) n (Hs.fgt q P n i x) := by
  change pull _ (dbl.inl P') _ n (pull _ (dbl.map φ) _ n x.1) = pull _ φ.right _ n (pull _ (dbl.inl P) _ n x.1)
  rw [← pull_comp, ← pull_comp, dbl.inl_map']

theorem res_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (y : Ht q P.right n i) :
    pull _ P'.hom (tw q i) n (pull _ φ.right (tw q i) n y) = pull _ φ.left (tw q i) n (pull _ P.hom (tw q i) n y) := by
  rw [← pull_comp, ← pull_comp, ← Arrow.w φ]

theorem pull_left_comp (q : ℕ) {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) (n i : ℤ) (y : Ht q P.left n i) :
    pull _ (φ ≫ ψ).left (tw q i) n y = pull _ φ.left (tw q i) n (pull _ ψ.left (tw q i) n y) := by
  rw [Arrow.comp_left, pull_comp]

theorem pull_right_comp (q : ℕ) {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) (n i : ℤ) (y : Ht q P.right n i) :
    pull _ (φ ≫ ψ).right (tw q i) n y = pull _ φ.right (tw q i) n (pull _ ψ.right (tw q i) n y) := by
  rw [Arrow.comp_right, pull_comp]

theorem leafHsFive : LeafHsFive := by
  intro a1 b1 hBd q A B _ _ φ I hq J _ _ D s t hc he i hO n
  obtain ⟨δ, hδ⟩ := hBd
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have hqB : IsUnit (q : B) := by simpa using hq.map φ
  have hqj : ∀ j, IsUnit (q : D.obj j) := fun j => by simpa using hq.map (s.app j).hom
  have hsn : ∀ {j k : J} (f : j ⟶ k), s.app k = s.app j ≫ D.map f := fun f => by simpa using s.naturality f
  have htn : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ t.app k = t.app j := fun f => by simpa using t.naturality f
  have hD : ∀ {j k : J} (f : j ⟶ k), off (D.obj k) (I.map (s.app k).hom) ≤
      Spec.map (D.map f) ⁻¹ᵁ off (D.obj j) (I.map (s.app j).hom) := by
    intro j k f
    have e1 := off_map (s.app k).hom I
    have e2 := off_map (s.app j).hom I
    simp only [CommRingCat.ofHom_hom] at e1 e2
    rw [e1, e2, hsn f, Spec.map_comp]
    intro x hx; exact hx
  have hT : ∀ j, off B (I.map φ) ≤ Spec.map (t.app j) ⁻¹ᵁ off (D.obj j) (I.map (s.app j).hom) := by
    intro j
    have e1 := off_map φ I
    have e2 := off_map (s.app j).hom I
    simp only [CommRingCat.ofHom_hom] at e2
    rw [e1, e2, ← he j, Spec.map_comp]
    intro x hx; exact hx
  have eT : ∀ {j k : J} (f : j ⟶ k), Spec.map (t.app j) = Spec.map (t.app k) ≫ Spec.map (D.map f) := fun f => by
    rw [← Spec.map_comp, htn f]
  have eD : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l), Spec.map (D.map (f ≫ g)) = Spec.map (D.map g) ≫ Spec.map (D.map f) :=
    fun f g => by rw [← Spec.map_comp, ← Functor.map_comp]
  have sc : ∀ k : ℤ, (∀ x : Ht q (opn (off B (I.map φ))).right k i, ∃ j, ∃ y : Ht q (opn (off (D.obj j) (I.map (s.app j).hom))).right k i,
      pull _ (opnMap (Spec.map (t.app j)) _ _ (hT j)).right (tw q i) k y = x) ∧
      ∀ j (y : Ht q (opn (off (D.obj j) (I.map (s.app j).hom))).right k i),
        pull _ (opnMap (Spec.map (t.app j)) _ _ (hT j)).right (tw q i) k y = 0 →
        ∃ (l : J) (f : j ⟶ l), pull _ (opnMap (Spec.map (D.map f)) _ _ (hD f)).right (tw q i) k y = 0 :=
    fun k => spec_cont b1 q D t hc hqB hqj k i
  have ex := fun {X : Scheme.{0}} (V : X.Opens) (k : ℤ) => hδ.1 q (opn V) (opn_mono V) k i
  constructor
  · intro x
    obtain ⟨j1, y1, hy1'⟩ := (sc (m + 1)).1 (Hs.fgt q _ (m + 1) i x)
    have h2 : pull _ (opnMap (Spec.map (t.app j1)) _ _ (hT j1)).left (tw q i) (m + 1)
        (pull _ (opn (off (D.obj j1) (I.map (s.app j1).hom))).hom (tw q i) (m + 1) y1) = 0 := by
      rw [← res_pull, hy1']
      exact (ex _ (m + 1)).1.apply_apply_eq_zero x
    obtain ⟨k, f, h', hk⟩ := (hO (m + 1)).2 j1 (hT j1) _ h2
    have h3 : pull _ (opn (off (D.obj k) (I.map (s.app k).hom))).hom (tw q i) (m + 1)
        (pull _ (opnMap (Spec.map (D.map f)) _ _ h').right (tw q i) (m + 1) y1) = 0 := by
      rw [res_pull]; exact hk
    obtain ⟨z, hz⟩ := ((ex (off (D.obj k) (I.map (s.app k).hom)) (m + 1)).1 _).1 h3
    have h4 : Hs.fgt q _ (m + 1) i (x - Hs.pull q (opnMap (Spec.map (t.app k)) _ _ (hT k)) (m + 1) i z) = 0 := by
      rw [map_sub, fgt_pull, hz, ← pull_right_comp,
        ← opnMap_tri (Spec.map (t.app k)) (Spec.map (D.map f)) (eT f) _ _ _ (hT j1) (hT k) h', hy1', sub_self]
    obtain ⟨w, hw⟩ := ((ex (off B (I.map φ)) m).2.2 _).1 h4
    obtain ⟨j2, h2', w2, hw2⟩ := (hO m).1 w
    refine ⟨IsFiltered.max k j2, hT _,
      Hs.pull q (opnMap (Spec.map (D.map (IsFiltered.leftToMax k j2))) _ _ (hD _)) (m + 1) i z +
      δ q _ m i (pull _ (opnMap (Spec.map (D.map (IsFiltered.rightToMax k j2))) _ _ (hD _)).left (tw q i) m w2), ?_⟩
    rw [map_add, ← Hs.pull_comp',
      ← opnMap_tri (Spec.map (t.app _)) (Spec.map (D.map (IsFiltered.leftToMax k j2))) (eT _) _ _ _ (hT k) (hT _) (hD _),
      hδ.2.1 q _ _ _ (opn_mono _) (opn_mono _), ← pull_left_comp,
      ← opnMap_tri (Spec.map (t.app _)) (Spec.map (D.map (IsFiltered.rightToMax k j2))) (eT _) _ _ _ h2' (hT _) (hD _),
      hw2, hw]
    abel
  · intro j h y hy
    have hf : pull _ (opnMap (Spec.map (t.app j)) _ _ h).right (tw q i) (m + 1) (Hs.fgt q _ (m + 1) i y) = 0 := by
      rw [← fgt_pull, hy, map_zero]
    obtain ⟨k, f, hk⟩ := (sc (m + 1)).2 j _ (by exact hf)
    have h5 : Hs.fgt q _ (m + 1) i (Hs.pull q (opnMap (Spec.map (D.map f)) _ _ (hD f)) (m + 1) i y) = 0 := by
      rw [fgt_pull]; exact hk
    obtain ⟨w, hw⟩ := ((ex (off (D.obj k) (I.map (s.app k).hom)) m).2.2 _).1 h5
    have h6 : δ q _ m i (pull _ (opnMap (Spec.map (t.app k)) _ _ (hT k)).left (tw q i) m w) = 0 := by
      rw [← hδ.2.1 q _ _ (opnMap (Spec.map (t.app k)) _ _ (hT k)) (opn_mono _) (opn_mono _), hw, ← Hs.pull_comp',
        ← opnMap_tri (Spec.map (t.app k)) (Spec.map (D.map f)) (eT f) _ _ _ h (hT k) (hD f), hy]
    obtain ⟨v, hv⟩ := ((ex (off B (I.map φ)) m).2.1 _).1 h6
    obtain ⟨j3, v3, hv3'⟩ := (sc m).1 v
    have h7 : pull _ (opnMap (Spec.map (t.app (IsFiltered.max k j3))) _ _ (hT _)).left (tw q i) m
        (pull _ (opnMap (Spec.map (D.map (IsFiltered.leftToMax k j3))) _ _ (hD _)).left (tw q i) m w -
          pull _ (opn (off (D.obj (IsFiltered.max k j3)) (I.map (s.app _).hom))).hom (tw q i) m
            (pull _ (opnMap (Spec.map (D.map (IsFiltered.rightToMax k j3))) _ _ (hD _)).right (tw q i) m v3)) = 0 := by
      rw [map_sub, sub_eq_zero, ← pull_left_comp,
        ← opnMap_tri (Spec.map (t.app _)) (Spec.map (D.map (IsFiltered.leftToMax k j3))) (eT _) _ _ _ (hT k) (hT _) (hD _),
        ← res_pull, ← pull_right_comp,
        ← opnMap_tri (Spec.map (t.app _)) (Spec.map (D.map (IsFiltered.rightToMax k j3))) (eT _) _ _ _ (hT j3) (hT _) (hD _),
        hv3', hv]
    obtain ⟨r, g, h8, hr⟩ := (hO m).2 _ (hT _) _ h7
    refine ⟨r, f ≫ IsFiltered.leftToMax k j3 ≫ g, hD _, ?_⟩
    rw [map_sub, sub_eq_zero] at hr
    rw [opnMap_tri (Spec.map (D.map (IsFiltered.leftToMax k j3 ≫ g))) (Spec.map (D.map f)) (eD _ _) _ _ _ _ (hD _) (hD f),
      Hs.pull_comp', ← hw,
      opnMap_tri (Spec.map (D.map g)) (Spec.map (D.map (IsFiltered.leftToMax k j3))) (eD _ _) _ _ _ _ h8 (hD _),
      Hs.pull_comp', hδ.2.1 q _ _ _ (opn_mono _) (opn_mono _), hδ.2.1 q _ _ _ (opn_mono _) (opn_mono _), hr,
      ← res_pull]
    exact (ex _ m).2.1.apply_apply_eq_zero _

theorem leafHsCont_of' (hB : LeafBd) (hE : LeafExc) (hO : LeafOffCont) : LeafHsCont :=
  leafHsCont_of hB hE hO leafHsFive

end LateralTheory.CohomologicalPurity
