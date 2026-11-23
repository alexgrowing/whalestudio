import Development.EtaleCohomology.CohomologicalPurity.LeafIndExcPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def HtOffCont (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) {J : Type} [SmallCategory J]
    (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
    (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)) (n i : ℤ) : Prop :=
  (∀ x : Ht q (opn (off B (I.map φ))).left n i, ∃ j h, ∃ y,
    pull _ (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h).left (tw q i) n y = x) ∧
  (∀ j h y, pull _ (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h).left
      (tw q i) n y = 0 →
    ∃ (k : J) (f : j ⟶ k) (h' : _), pull _ (opnMap (Spec.map (D.map f)) (off (D.obj k) (I.map (s.app k).hom))
      (off (D.obj j) (I.map (s.app j).hom)) h').left (tw q i) n y = 0)

def LeafOffCont : Prop := A1 → A4 → B1 → LeafBd → LeafExc → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B]
  (φ : A →+* B) (I : Ideal A), I.FG → IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ, HtOffCont q φ I D s t n i

def LeafHsFive : Prop := A1 → B1 → LeafBd → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
  (I : Ideal A), IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D) (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ i : ℤ,
  (∀ m : ℤ, HtOffCont q φ I D s t m i) → ∀ n : ℤ,
  (∀ x : Hs q (opn (off B (I.map φ))) n i, ∃ j h, ∃ y,
    Hs.pull q (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h) n i y = x) ∧
  (∀ j h y, Hs.pull q (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h) n i y = 0 →
    ∃ (k : J) (f : j ⟶ k) (h' : _), Hs.pull q (opnMap (Spec.map (D.map f)) (off (D.obj k) (I.map (s.app k).hom))
      (off (D.obj j) (I.map (s.app j).hom)) h') n i y = 0)

theorem opn_mono {X : Scheme.{0}} (U : X.Opens) : Mono (opn U).hom := by
  change Mono (sch.map U.ι)
  unfold sch
  infer_instance

theorem spec_cont (b1 : B1) (q : ℕ) {B : Type} [CommRing B] {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)) (hc : IsColimit (Cocone.mk _ t))
    (hq : IsUnit (q : B)) (hqj : ∀ j, IsUnit (q : D.obj j)) (n i : ℤ) :
    (∀ x : Ht q (sp B) n i, ∃ j, ∃ y, pull _ (sch.map (Spec.map (t.app j))) (tw q i) n y = x) ∧
    ∀ j (y : Ht q (sch.obj (Spec (D.obj j))) n i), pull _ (sch.map (Spec.map (t.app j))) (tw q i) n y = 0 →
      ∃ (k : J) (f : j ⟶ k), pull _ (sch.map (Spec.map (D.map f))) (tw q i) n y = 0 := by
  have h := b1 q D _ hc n i
  exact ⟨fun x => h.1 x hq, fun j y hy => h.2 j y (hqj j) hy⟩

theorem leafHsCont_of (hB : LeafBd) (hE : LeafExc) (hO : LeafOffCont) (hF : LeafHsFive) : LeafHsCont := by
  intro a1 a4 b1 q A B _ _ φ I hI hq J _ _ D s t hc he n i
  exact hF a1 b1 hB q φ I hq J D s t hc he i (fun m => hO a1 a4 b1 hB hE q φ I hI hq J D s t hc he m i) n

end LateralTheory.CohomologicalPurity
