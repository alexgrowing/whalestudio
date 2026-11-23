import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def LeafNbhdExc : Prop := A1 → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A),
  Nbhd φ I → IsUnit (q : A) → ∀ h, Exc q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B (I.map φ)) (off A I) h)

def LeafHsCont : Prop := A1 → A4 → B1 → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A),
  I.FG → IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D) (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ,
  (∀ x : Hs q (opn (off B (I.map φ))) n i, ∃ j h, ∃ y,
    Hs.pull q (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h) n i y = x) ∧
  (∀ j h y, Hs.pull q (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h) n i y = 0 →
    ∃ (k : J) (f : j ⟶ k) (h' : _), Hs.pull q (opnMap (Spec.map (D.map f)) (off (D.obj k) (I.map (s.app k).hom))
      (off (D.obj j) (I.map (s.app j).hom)) h') n i y = 0)

theorem off_map {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (J : Ideal R) :
    off S (J.map ψ) = Spec.map (CommRingCat.ofHom ψ) ⁻¹ᵁ off R J := by
  ext x
  show ¬ ((Ideal.map ψ J : Set S) ⊆ (x : PrimeSpectrum S).asIdeal) ↔
    ¬ ((J : Set R) ⊆ (PrimeSpectrum.comap ψ x).asIdeal)
  simp only [SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap]
  exact Iff.rfl

theorem dbl.inl_map' {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc _ _ _

theorem dbl.map_comp' {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) :
    dbl.map (φ ≫ ψ) = dbl.map φ ≫ dbl.map ψ := by
  apply pushout.hom_ext
  · change dbl.inl P'' ≫ dbl.map (φ ≫ ψ) = dbl.inl P'' ≫ dbl.map φ ≫ dbl.map ψ
    rw [dbl.inl_map', ← Category.assoc, dbl.inl_map', Category.assoc, dbl.inl_map', Arrow.comp_right,
      Category.assoc]
  · change dbl.inr P'' ≫ dbl.map (φ ≫ ψ) = dbl.inr P'' ≫ dbl.map φ ≫ dbl.map ψ
    rw [dbl.inr_map, ← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, Arrow.comp_right,
      Category.assoc]

theorem Hs.pull_comp' (q : ℕ) {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q (φ ≫ ψ) n i x = Hs.pull q φ n i (Hs.pull q ψ n i x) := by
  apply Subtype.ext
  change GlobalTheory.EtC.pull _ (dbl.map (φ ≫ ψ)) _ n x.1 = GlobalTheory.EtC.pull _ (dbl.map φ) _ n (GlobalTheory.EtC.pull _ (dbl.map ψ) _ n x.1)
  rw [dbl.map_comp', pull_comp]

theorem opnMap_comp {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) (U'' : X''.Opens) (U' : X'.Opens)
    (U : X.Opens) (h1 : U'' ≤ f ⁻¹ᵁ U') (h2 : U' ≤ g ⁻¹ᵁ U) (h : U'' ≤ (f ≫ g) ⁻¹ᵁ U) :
    opnMap (f ≫ g) U'' U h = opnMap f U'' U' h1 ≫ opnMap g U' U h2 := by
  apply Arrow.hom_ext
  · change sch.map _ = sch.map _ ≫ sch.map _
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map _ = sch.map _ ≫ sch.map _
    rw [Functor.map_comp]

theorem opnMap_congr {X' X : Scheme.{0}} {f g : X' ⟶ X} (e : f = g) (U' : X'.Opens) (U : X.Opens) (h : U' ≤ f ⁻¹ᵁ U)
    (h' : U' ≤ g ⁻¹ᵁ U) : opnMap f U' U h = opnMap g U' U h' := by
  subst e; rfl

theorem leafIndExc_of (hN : LeafNbhdExc) (hC : LeafHsCont) : LeafIndExc := by
  intro a1 a4 b1 q A B _ _ φ I hI hInd hq h n i
  obtain ⟨J, _, _, D, s, t, ⟨hcol⟩, hst⟩ := hInd
  have hs : ∀ j, Nbhd (A := A) (s.app j).hom I := fun j => (hst j).1
  have he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ := fun j => (hst j).2
  obtain ⟨hsurj, hinj⟩ := hC a1 a4 b1 q φ I hI hq J D s t hcol he n i
  have hsle : ∀ j, off (D.obj j) (I.map (s.app j).hom) ≤ Spec.map (s.app j) ⁻¹ᵁ off A I := fun j =>
    le_of_eq (off_map (s.app j).hom I)
  have hE : ∀ j, Function.Bijective (Hs.pull q (opnMap (Spec.map (s.app j)) _ _ (hsle j)) n i) := fun j =>
    hN a1 q (s.app j).hom I (hs j) hq (hsle j) n i
  have hB : ∀ j, off B (I.map φ) ≤ Spec.map (t.app j) ⁻¹ᵁ off (D.obj j) (I.map (s.app j).hom) := fun j => by
    intro x hx
    have hx' := h hx
    rw [← he j, Spec.map_comp] at hx'
    have e := off_map (s.app j).hom I
    simp only [CommRingCat.ofHom_hom] at e
    rw [e]
    exact hx'
  have hfac : ∀ j (h1 : off B (I.map φ) ≤ Spec.map (t.app j) ⁻¹ᵁ off (D.obj j) (I.map (s.app j).hom)),
      opnMap (Spec.map (CommRingCat.ofHom φ)) (off B (I.map φ)) (off A I) h =
        opnMap (Spec.map (t.app j)) _ _ h1 ≫ opnMap (Spec.map (s.app j)) _ _ (hsle j) := by
    intro j h1
    have hcomp : off B (I.map φ) ≤ (Spec.map (t.app j) ≫ Spec.map (s.app j)) ⁻¹ᵁ off A I := by
      rw [← Spec.map_comp, he j]; exact h
    exact (opnMap_congr (by rw [← Spec.map_comp, he j]) _ _ _ hcomp).trans
      (opnMap_comp _ _ _ _ _ h1 (hsle j) hcomp)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    rw [hfac j (hB j), Hs.pull_comp'] at hz
    obtain ⟨k, f, h', hk⟩ := hinj j (hB j) _ hz
    have hn : s.app k = s.app j ≫ D.map f := by
      have := s.naturality f
      simpa using this
    have hk' : opnMap (Spec.map (s.app k)) _ _ (hsle k) =
        opnMap (Spec.map (D.map f)) _ _ h' ≫ opnMap (Spec.map (s.app j)) _ _ (hsle j) := by
      have hcomp : off (D.obj k) (I.map (s.app k).hom) ≤ (Spec.map (D.map f) ≫ Spec.map (s.app j)) ⁻¹ᵁ off A I := by
        rw [← Spec.map_comp, ← hn]; exact hsle k
      exact (opnMap_congr (by rw [← Spec.map_comp, ← hn]) _ _ _ hcomp).trans
        (opnMap_comp _ _ _ _ _ h' (hsle j) hcomp)
    apply (injective_iff_map_eq_zero _).1 (hE k).1
    rw [hk', Hs.pull_comp', hk]
  · intro x
    obtain ⟨j, h1, y, hy⟩ := hsurj x
    obtain ⟨z, hz⟩ := (hE j).2 y
    exact ⟨z, by rw [hfac j h1, Hs.pull_comp', hz, hy]⟩

end LateralTheory.CohomologicalPurity
