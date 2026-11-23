import Development.EtaleCohomology.CohomologicalPurity.EtalePurityContinuityOffClosedOfLocalAndChase

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem contS_exc (q : ℕ) {J : Type} [SmallCategory J] (FA FB : Jᵒᵖ ⥤ Arrow Spc) (PA PB : Arrow Spc)
    (cA : ∀ j, PA ⟶ FA.obj (op j)) (cB : ∀ j, PB ⟶ FB.obj (op j)) (e : FA ⟶ FB) (e0 : PA ⟶ PB)
    (he : ∀ j, cA j ≫ e.app (op j) = e0 ≫ cB j) (hE : ∀ j, Exc q (e.app (op j))) (hE0 : Exc q e0) (n i : ℤ)
    (hS : ContS q FA PA cA n i) : ContS q FB PB cB n i := by
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨j, y, hy⟩ := hS.1 (Hs.pull q e0 n i x)
    obtain ⟨z, rfl⟩ := (hE j n i).2 y
    refine ⟨j, z, (hE0 n i).1 ?_⟩
    rw [← hy, ← Hs.pull_comp', ← Hs.pull_comp', he]
  · have h0 : Hs.pull q (cA j) n i (Hs.pull q (e.app (op j)) n i y) = 0 := by
      rw [← Hs.pull_comp', he, Hs.pull_comp', hy, map_zero]
    obtain ⟨k, f, hk⟩ := hS.2 j _ h0
    refine ⟨k, f, (hE k n i).1 ?_⟩
    rw [map_zero, ← Hs.pull_comp', ← e.naturality, Hs.pull_comp', hk]

theorem chase_abs (hS5 : PairFiveS) (hR5 : PairFiveR) (bd : LeafBd) (q : ℕ) {J : Type} [SmallCategory J] [IsFiltered J]
    (FA FB : Jᵒᵖ ⥤ Arrow Spc) (PA PB : Arrow Spc)
    (cA : ∀ j, PA ⟶ FA.obj (op j)) (cB : ∀ j, PB ⟶ FB.obj (op j))
    (hcA : ∀ j k (f : j ⟶ k), cA k ≫ FA.map f.op = cA j) (hcB : ∀ j k (f : j ⟶ k), cB k ≫ FB.map f.op = cB j)
    (hmA : ∀ j, Mono (FA.obj (op j)).hom) (hmB : ∀ j, Mono (FB.obj (op j)).hom) (hPA : Mono PA.hom) (hPB : Mono PB.hom)
    (e : FA ⟶ FB) (e0 : PA ⟶ PB)
    (he : ∀ j, cA j ≫ e.app (op j) = e0 ≫ cB j) (hE : ∀ j, Exc q (e.app (op j))) (hE0 : Exc q e0) (i : ℤ)
    (hAL : ∀ m, ContL q FA PA cA m i) (hAR : ∀ m, ContR q FA PA cA m i) (hBL : ∀ m, ContL q FB PB cB m i) :
    ∀ n, ContR q FB PB cB n i :=
  hR5 bd q FB PB cB hcB hmB hPB i hBL
    (fun m => contS_exc q FA FB PA PB cA cB e e0 he hE hE0 m i (hS5 bd q FA PA cA hcA hmA hPA i hAL hAR m))

theorem resLE_id' {X : Scheme.{0}} (U : X.Opens) (h : U ≤ (𝟙 X) ⁻¹ᵁ U) : Scheme.Hom.resLE (𝟙 X) U U h = 𝟙 _ := by
  rw [← cancel_mono U.ι, Scheme.Hom.resLE_comp_ι, Category.comp_id, Category.id_comp]

theorem opnMap_id {X : Scheme.{0}} (U : X.Opens) (h : U ≤ (𝟙 X) ⁻¹ᵁ U) : opnMap (𝟙 X) U U h = 𝟙 _ := by
  apply Arrow.hom_ext
  · change sch.map _ = 𝟙 _
    rw [resLE_id']; exact sch.map_id _
  · exact sch.map_id X

theorem mapA_le {X' X : Scheme.{0}} (f : X' ⟶ X) (U V : X.Opens) (U' V' : X'.Opens) (hU : U' ≤ f ⁻¹ᵁ U)
    (hV : V' ≤ f ⁻¹ᵁ V) : V'.ι ⁻¹ᵁ U' ≤ (f.resLE V V' hV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U) := by
  intro x hx
  change V.ι ((f.resLE V V' hV) x) ∈ U
  rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
  exact hU hx

def mapA {X' X : Scheme.{0}} (f : X' ⟶ X) (U V : X.Opens) (U' V' : X'.Opens) (hU : U' ≤ f ⁻¹ᵁ U)
    (hV : V' ≤ f ⁻¹ᵁ V) : opn (V'.ι ⁻¹ᵁ U') ⟶ opn (V.ι ⁻¹ᵁ U) :=
  opnMap (f.resLE V V' hV) _ _ (mapA_le f U V U' V' hU hV)

theorem mapA_congr {X' X : Scheme.{0}} {f g : X' ⟶ X} (e : f = g) (U V : X.Opens) (U' V' : X'.Opens)
    (hU : U' ≤ f ⁻¹ᵁ U) (hV : V' ≤ f ⁻¹ᵁ V) (hU' : U' ≤ g ⁻¹ᵁ U) (hV' : V' ≤ g ⁻¹ᵁ V) :
    mapA f U V U' V' hU hV = mapA g U V U' V' hU' hV' := by
  subst e; rfl

theorem mapA_id {X : Scheme.{0}} (U V : X.Opens) (hU : U ≤ (𝟙 X) ⁻¹ᵁ U) (hV : V ≤ (𝟙 X) ⁻¹ᵁ V) :
    mapA (𝟙 X) U V U V hU hV = 𝟙 _ := by
  unfold mapA
  rw [opnMap_congr (resLE_id' V hV), ← opnMap_id]
  · rfl

theorem mapA_comp {X'' X' X : Scheme.{0}} (g : X'' ⟶ X') (f : X' ⟶ X) (U V : X.Opens) (U' V' : X'.Opens)
    (U'' V'' : X''.Opens) (hU : U' ≤ f ⁻¹ᵁ U) (hV : V' ≤ f ⁻¹ᵁ V) (hU' : U'' ≤ g ⁻¹ᵁ U') (hV' : V'' ≤ g ⁻¹ᵁ V')
    (hU2 : U'' ≤ (g ≫ f) ⁻¹ᵁ U) (hV2 : V'' ≤ (g ≫ f) ⁻¹ᵁ V) :
    mapA g U' V' U'' V'' hU' hV' ≫ mapA f U V U' V' hU hV = mapA (g ≫ f) U V U'' V'' hU2 hV2 := by
  have e : g.resLE V' V'' hV' ≫ f.resLE V V' hV = (g ≫ f).resLE V V'' hV2 := by
    rw [Scheme.Hom.resLE_comp_resLE]
  have h : V''.ι ⁻¹ᵁ U'' ≤ (g.resLE V' V'' hV' ≫ f.resLE V V' hV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U) := by
    rw [e]; exact mapA_le (g ≫ f) U V U'' V'' hU2 hV2
  unfold mapA
  rw [← opnMap_comp _ _ _ _ _ _ _ h]
  exact opnMap_congr e _ _ _ _

section Sys
variable {A : Type} [CommRing A] {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0})
  (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)

def oj (I : Ideal A) (j : J) : (Spec (D.obj j)).Opens := off (D.obj j) (I.map (s.app j).hom)

theorem s_nat {j k : J} (f : j ⟶ k) : s.app k = s.app j ≫ D.map f := by
  have := s.naturality f
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
  exact this

theorem oj_pre (I : Ideal A) {j k : J} (f : j ⟶ k) : oj D s I k = Spec.map (D.map f) ⁻¹ᵁ oj D s I j := by
  unfold oj
  rw [s_nat D s f, CommRingCat.hom_comp]
  exact off_map_comp I (s.app j).hom (D.map f).hom

theorem ojsup_pre (I1 I2 : Ideal A) {j k : J} (f : j ⟶ k) :
    oj D s I1 k ⊔ oj D s I2 k ≤ Spec.map (D.map f) ⁻¹ᵁ (oj D s I1 j ⊔ oj D s I2 j) := by
  intro x hx
  rw [oj_pre D s I1 f, oj_pre D s I2 f] at hx
  exact hx

def sysU (U V : ∀ j, (Spec (D.obj j)).Opens) (hU : ∀ j k (f : j ⟶ k), U k ≤ Spec.map (D.map f) ⁻¹ᵁ U j)
    (hV : ∀ j k (f : j ⟶ k), V k ≤ Spec.map (D.map f) ⁻¹ᵁ V j) : Jᵒᵖ ⥤ Arrow Spc where
  obj j := opn ((V j.unop).ι ⁻¹ᵁ U j.unop)
  map f := mapA (Spec.map (D.map f.unop)) _ _ _ _ (hU _ _ f.unop) (hV _ _ f.unop)
  map_id j := by
    have e : Spec.map (D.map (𝟙 j).unop) = 𝟙 _ := by rw [unop_id, D.map_id, Spec.map_id]
    exact (mapA_congr e _ _ _ _ _ _ (fun x hx => hx) (fun x hx => hx)).trans (mapA_id _ _ _ _)
  map_comp {a b c} f g := by
    have e : Spec.map (D.map (f ≫ g).unop) = Spec.map (D.map f.unop) ≫ Spec.map (D.map g.unop) := by
      rw [unop_comp, D.map_comp, Spec.map_comp]
    exact (mapA_congr e _ _ _ _ _ _ (fun x hx => hU _ _ g.unop (hU _ _ f.unop hx))
      (fun x hx => hV _ _ g.unop (hV _ _ f.unop hx))).trans (mapA_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _).symm

end Sys

theorem exc_nat {X' X : Scheme.{0}} (f : X' ⟶ X) (U V : X.Opens) (U' V' : X'.Opens) (hU : U' ≤ f ⁻¹ᵁ U)
    (hV : V' ≤ f ⁻¹ᵁ V) (hW : U' ⊔ V' ≤ f ⁻¹ᵁ (U ⊔ V)) :
    mapA f U V U' V' hU hV ≫ excMap U V = excMap U' V' ≫ mapA f U (U ⊔ V) U' (U' ⊔ V') hU hW := by
  apply Arrow.hom_ext
  · change sch.map _ ≫ sch.map _ = sch.map _ ≫ sch.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    rw [← cancel_mono (Scheme.Opens.ι _), ← cancel_mono (Scheme.Opens.ι _)]
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι_assoc,
      Scheme.homOfLE_ι_assoc]
  · change sch.map _ ≫ sch.map _ = sch.map _ ≫ sch.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc]

section Glue
variable {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I1 I2 : Ideal A) {J : Type} [SmallCategory J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B))

theorem oinf_pre (I : Ideal A) (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) (j : J) :
    off B (I.map φ) = Spec.map (t.app j) ⁻¹ᵁ oj D s I j := by
  have h : φ = (t.app j).hom.comp (s.app j).hom := by rw [← CommRingCat.hom_comp, he]; rfl
  unfold oj
  rw [h]
  exact off_map_comp I (s.app j).hom (t.app j).hom

def sysA : Jᵒᵖ ⥤ Arrow Spc :=
  sysU D (oj D s I1) (oj D s I2) (fun _ _ f => (oj_pre D s I1 f).le) (fun _ _ f => (oj_pre D s I2 f).le)

def sysB : Jᵒᵖ ⥤ Arrow Spc :=
  sysU D (oj D s I1) (fun j => oj D s I1 j ⊔ oj D s I2 j) (fun _ _ f => (oj_pre D s I1 f).le)
    (fun _ _ f => ojsup_pre D s I1 I2 f)

def limA : Arrow Spc := opn ((off B (I2.map φ)).ι ⁻¹ᵁ off B (I1.map φ))
def limB : Arrow Spc := opn ((off B (I1.map φ) ⊔ off B (I2.map φ)).ι ⁻¹ᵁ off B (I1.map φ))

def conA (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) (j : J) : limA φ I1 I2 ⟶ (sysA I1 I2 D s).obj (op j) :=
  mapA (Spec.map (t.app j)) _ _ _ _ (oinf_pre φ D s t I1 he j).le (oinf_pre φ D s t I2 he j).le

theorem oinfsup_pre (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) (j : J) :
    off B (I1.map φ) ⊔ off B (I2.map φ) ≤ Spec.map (t.app j) ⁻¹ᵁ (oj D s I1 j ⊔ oj D s I2 j) := by
  intro x hx
  rw [oinf_pre φ D s t I1 he j, oinf_pre φ D s t I2 he j] at hx
  exact hx

def conB (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) (j : J) : limB φ I1 I2 ⟶ (sysB I1 I2 D s).obj (op j) :=
  mapA (Spec.map (t.app j)) _ _ _ _ (oinf_pre φ D s t I1 he j).le (oinfsup_pre φ I1 I2 D s t he j)

def excAB : sysA I1 I2 D s ⟶ sysB I1 I2 D s where
  app j := excMap (oj D s I1 j.unop) (oj D s I2 j.unop)
  naturality a b f := exc_nat _ _ _ _ _ (oj_pre D s I1 f.unop).le (oj_pre D s I2 f.unop).le _

theorem t_nat {j k : J} (f : j ⟶ k) : D.map f ≫ t.app k = t.app j := by
  have := t.naturality f
  simpa using this

theorem conA_comp (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) (j k : J) (f : j ⟶ k) :
    conA φ I1 I2 D s t he k ≫ (sysA I1 I2 D s).map f.op = conA φ I1 I2 D s t he j := by
  have e : Spec.map (t.app k) ≫ Spec.map (D.map f) = Spec.map (t.app j) := by
    rw [← Spec.map_comp, t_nat D t f]
  exact (mapA_comp (Spec.map (t.app k)) (Spec.map (D.map f)) (oj D s I1 j) (oj D s I2 j) (oj D s I1 k) (oj D s I2 k)
    (off B (I1.map φ)) (off B (I2.map φ)) (oj_pre D s I1 f).le ((oj_pre D s I2 f).le) (oinf_pre φ D s t I1 he k).le ((oinf_pre φ D s t I2 he k).le)
    (by rw [e]; exact (oinf_pre φ D s t I1 he j).le) (by rw [e]; exact (oinf_pre φ D s t I2 he j).le)).trans (mapA_congr e _ _ _ _ _ _ _ _)

theorem conB_comp (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) (j k : J) (f : j ⟶ k) :
    conB φ I1 I2 D s t he k ≫ (sysB I1 I2 D s).map f.op = conB φ I1 I2 D s t he j := by
  have e : Spec.map (t.app k) ≫ Spec.map (D.map f) = Spec.map (t.app j) := by
    rw [← Spec.map_comp, t_nat D t f]
  exact (mapA_comp (Spec.map (t.app k)) (Spec.map (D.map f)) (oj D s I1 j) (oj D s I1 j ⊔ oj D s I2 j) (oj D s I1 k) (oj D s I1 k ⊔ oj D s I2 k)
    (off B (I1.map φ)) (off B (I1.map φ) ⊔ off B (I2.map φ)) (oj_pre D s I1 f).le (ojsup_pre D s I1 I2 f) (oinf_pre φ D s t I1 he k).le (oinfsup_pre φ I1 I2 D s t he k)
    (by rw [e]; exact (oinf_pre φ D s t I1 he j).le) (by rw [e]; exact oinfsup_pre φ I1 I2 D s t he j)).trans (mapA_congr e _ _ _ _ _ _ _ _)

theorem conAB (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) (j : J) :
    conA φ I1 I2 D s t he j ≫ (excAB I1 I2 D s).app (op j) =
      excMap (off B (I1.map φ)) (off B (I2.map φ)) ≫ conB φ I1 I2 D s t he j :=
  exc_nat _ _ _ _ _ _ _ _

end Glue

section Leaves

theorem contR_A (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I1 I2 : Ideal A) {J : Type}
    [SmallCategory J] (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
    (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)) (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ)
    (m i : ℤ) (H : HtOffCont q φ I2 D s t m i) :
    ContR q (sysA I1 I2 D s) (limA φ I1 I2) (conA φ I1 I2 D s t he) m i := by
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨j, _h, y, hy⟩ := H.1 x
    exact ⟨j, y, hy⟩
  · obtain ⟨k, f, _h, hk⟩ := H.2 j (oinf_pre φ D s t I2 he j).le y hy
    exact ⟨k, f, hk⟩

def OCG_AL : Prop := ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I1 I2 : Ideal A) (J : Type)
  [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)), IsColimit (Cocone.mk _ t) →
  ∀ (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) (m i : ℤ), HtOffCont q φ (I1 * I2) D s t m i →
  ContL q (sysA I1 I2 D s) (limA φ I1 I2) (conA φ I1 I2 D s t he) m i

def OCG_BL : Prop := ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I1 I2 : Ideal A) (J : Type)
  [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)), IsColimit (Cocone.mk _ t) →
  ∀ (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) (m i : ℤ), HtOffCont q φ I1 D s t m i →
  ContL q (sysB I1 I2 D s) (limB φ I1 I2) (conB φ I1 I2 D s t he) m i

def OCG_BR : Prop := ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I1 I2 : Ideal A) (J : Type)
  [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)), IsColimit (Cocone.mk _ t) →
  ∀ (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) (n i : ℤ),
  ContR q (sysB I1 I2 D s) (limB φ I1 I2) (conB φ I1 I2 D s t he) n i → HtOffCont q φ (I1 ⊔ I2) D s t n i

end Leaves

theorem OffChaseGeo_of (hAL : OCG_AL) (hBL : OCG_BL) (hBR : OCG_BR) : OffChaseGeo := by
  intro hS5 hR5 bd exc q A B _ _ φ I1 I2 _ J _ _ D s t hc he i h1 h2 h12 n
  exact hBR q φ I1 I2 J D s t hc he n i
    (chase_abs hS5 hR5 bd q (sysA I1 I2 D s) (sysB I1 I2 D s) (limA φ I1 I2) (limB φ I1 I2)
      (conA φ I1 I2 D s t he) (conB φ I1 I2 D s t he) (conA_comp φ I1 I2 D s t he) (conB_comp φ I1 I2 D s t he)
      (fun _ => opn_mono _) (fun _ => opn_mono _) (opn_mono _) (opn_mono _) (excAB I1 I2 D s)
      (excMap (off B (I1.map φ)) (off B (I2.map φ))) (conAB φ I1 I2 D s t he)
      (fun j => exc q _ _ _) (exc q _ _ _) i
      (fun m => hAL q φ I1 I2 J D s t hc he m i (h12 m))
      (fun m => contR_A q φ I1 I2 D s t he m i (h2 m))
      (fun m => hBL q φ I1 I2 J D s t hc he m i (h1 m)) n)

end LateralTheory.CohomologicalPurity
