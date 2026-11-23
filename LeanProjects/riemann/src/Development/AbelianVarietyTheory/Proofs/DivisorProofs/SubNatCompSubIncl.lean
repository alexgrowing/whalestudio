import Mathlib

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace GlobalTheory.QcSub

variable {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)

def gen {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) : Subring (F.obj (op W)) :=
  Subring.closure (Set.range (α.app (op W)).hom ∪ (F.map (homOfLE h).op).hom '' T)

lemma algebraMap_mem_gen {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) (r : Γ(X, W)) :
    (α.app (op W)).hom r ∈ gen F α h T :=
  Subring.subset_closure (Or.inl ⟨r, rfl⟩)

lemma res_mem_gen {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) {t : F.obj (op V)}
    (ht : t ∈ T) : (F.map (homOfLE h).op).hom t ∈ gen F α h T :=
  Subring.subset_closure (Or.inr ⟨t, ht, rfl⟩)

lemma map_gen_le {V W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) (T : Set (F.obj (op V))) :
    (gen F α h T).map (F.map (homOfLE h').op).hom ≤ gen F α (h'.trans h) T := by
  rw [gen, RingHom.map_closure, Subring.closure_le]
  rintro _ ⟨y, (⟨r, rfl⟩ | ⟨t, ht, rfl⟩), rfl⟩
  · have := congr($(α.naturality (homOfLE h').op).hom r)
    simp only [CommRingCat.comp_apply] at this
    rw [← this]
    exact algebraMap_mem_gen F α _ T _
  · rw [← CommRingCat.comp_apply, ← F.map_comp]
    exact res_mem_gen F α _ T ht

lemma res_mem_gen_of_mem {V W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) (T : Set (F.obj (op V)))
    {b : F.obj (op W)} (hb : b ∈ gen F α h T) :
    (F.map (homOfLE h').op).hom b ∈ gen F α (h'.trans h) T :=
  map_gen_le F α h h' T ⟨b, hb, rfl⟩

lemma gen_eq_adjoin {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) :
    letI := (α.app (op W)).hom.toAlgebra
    gen F α h T = (Algebra.adjoin Γ(X, W) ((F.map (homOfLE h).op).hom '' T)).toSubring := by
  letI := (α.app (op W)).hom.toAlgebra
  rw [Algebra.adjoin_eq_ring_closure]
  rfl

variable {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j))))

def sub (W : X.Opens) : Subring (F.obj (op W)) :=
  ⨅ (j : ι) (W' : X.Opens) (_ : IsAffineOpen W') (hW : W' ≤ W) (hV : W' ≤ V j),
    (gen F α hV (T j)).comap (F.map (homOfLE hW).op).hom

lemma mem_sub {W : X.Opens} {b : F.obj (op W)} :
    b ∈ sub F α V T W ↔ ∀ (j : ι) (W' : X.Opens), IsAffineOpen W' → ∀ (hW : W' ≤ W)
      (hV : W' ≤ V j), (F.map (homOfLE hW).op).hom b ∈ gen F α hV (T j) := by
  simp only [sub, Subring.mem_iInf, Subring.mem_comap]

lemma algebraMap_mem_sub (W : X.Opens) (r : Γ(X, W)) : (α.app (op W)).hom r ∈ sub F α V T W := by
  rw [mem_sub]
  intro j W' _ hW hV
  have := congr($(α.naturality (homOfLE hW).op).hom r)
  simp only [CommRingCat.comp_apply] at this
  rw [← this]
  exact algebraMap_mem_gen F α _ _ _

lemma res_mem_sub {W W₁ : X.Opens} (h : W₁ ≤ W) {b : F.obj (op W)} (hb : b ∈ sub F α V T W) :
    (F.map (homOfLE h).op).hom b ∈ sub F α V T W₁ := by
  rw [mem_sub] at hb ⊢
  intro j W' hW' hW hV
  rw [← CommRingCat.comp_apply, ← F.map_comp]
  exact hb j W' hW' (hW.trans h) hV

def subMap (W : X.Opens) : Γ(X, W) →+* sub F α V T W :=
  (α.app (op W)).hom.codRestrict _ (algebraMap_mem_sub F α V T W)

@[simps obj]
def subFunctor : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj W := CommRingCat.of (sub F α V T W.unop.1)
  map {W W₁} f := CommRingCat.ofHom
    ((F.map ((Scheme.AffineZariskiSite.toOpensFunctor X).map f.unop).op).hom.restrict _ _
      (fun _ hb ↦ res_mem_sub F α V T _ hb))
  map_id W := by
    ext b
    change (F.map _).hom b.1 = b.1
    rw [Subsingleton.elim ((Scheme.AffineZariskiSite.toOpensFunctor X).map (𝟙 W).unop).op (𝟙 _)]
    erw [F.map_id]
    rfl
  map_comp {W₁ W₂ W₃} f g := by
    ext b
    change (F.map _).hom b.1 = (F.map _).hom ((F.map _).hom b.1)
    rw [← CommRingCat.comp_apply]
    erw [← F.map_comp]
    rfl

def subNat : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ subFunctor F α V T where
  app W := CommRingCat.ofHom (subMap F α V T W.unop.1)
  naturality {W W₁} f := by
    ext r
    exact Subtype.ext congr($(α.naturality ((Scheme.AffineZariskiSite.toOpensFunctor X).map f.unop).op).hom r)

def subIncl : subFunctor F α V T ⟶ (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ F where
  app W := CommRingCat.ofHom (sub F α V T W.unop.1).subtype
  naturality _ _ _ := rfl

lemma subNat_comp_subIncl :
    subNat F α V T ≫ subIncl F α V T = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α :=
  rfl

lemma subIncl_injective (W : X.AffineZariskiSiteᵒᵖ) : Function.Injective ((subIncl F α V T).app W).hom :=
  Subtype.val_injective

lemma isLocalizationAway
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {W : X.Opens} (hW : IsAffineOpen W) (f : Γ(X, W)) :
    letI := (F.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    IsLocalization.Away ((α.app (op W)).hom f) (F.obj (op (X.basicOpen f))) :=
  Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mp hα ⟨W, hW⟩ f

end GlobalTheory.QcSub
