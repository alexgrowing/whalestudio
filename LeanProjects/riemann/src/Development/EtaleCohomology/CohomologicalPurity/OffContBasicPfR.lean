import Development.EtaleCohomology.CohomologicalPurity.LeafOffContPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

set_option backward.isDefEq.respectTransparency.types false in

def opIso {R : CommRingCat.{0}} (g : R) (U : (Spec R).Opens)
    (hU : U = PrimeSpectrum.basicOpen g) : U.toScheme ≅ Spec (CommRingCat.of (Localization.Away g)) :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι U) (Spec.map (CommRingCat.ofHom (algebraMap R _)))
    (by
      subst hU
      simp only [Scheme.Opens.range_ι]
      exact (PrimeSpectrum.localization_away_comap_range (Localization.Away g) g).symm)

theorem opIso_hom {R : CommRingCat.{0}} (g : R) (U : (Spec R).Opens)
    (hU : U = PrimeSpectrum.basicOpen g) :
    (opIso g U hU).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R _)) = U.ι := by
  simp [opIso]

theorem opIso_inv {R : CommRingCat.{0}} (g : R) (U : (Spec R).Opens)
    (hU : U = PrimeSpectrum.basicOpen g) :
    (opIso g U hU).inv ≫ U.ι = Spec.map (CommRingCat.ofHom (algebraMap R _)) := by
  rw [← opIso_hom g U hU, Iso.inv_hom_id_assoc]

def awMap {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (g : R) (g' : S) (hg : ψ g = g') :
    Localization.Away g →+* Localization.Away g' :=
  IsLocalization.map (M := Submonoid.powers g) (T := Submonoid.powers g') _ ψ
    (by rw [Submonoid.powers_le]; exact ⟨1, by simp [hg]⟩)

theorem awMap_alg {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (g : R) (g' : S) (hg : ψ g = g') :
    (awMap ψ g g' hg).comp (algebraMap R _) = (algebraMap S _).comp ψ := by
  ext x; simp [awMap, IsLocalization.map_eq]

theorem opIso_sq {R S : CommRingCat.{0}} (ψ : R ⟶ S) (g : R) (g' : S) (hg : ψ.hom g = g')
    (U : (Spec R).Opens) (hU : U = PrimeSpectrum.basicOpen g)
    (U' : (Spec S).Opens) (hU' : U' = PrimeSpectrum.basicOpen g')
    (h : U' ≤ Spec.map ψ ⁻¹ᵁ U) :
    (Spec.map ψ).resLE U U' h =
      (opIso g' U' hU').hom ≫ Spec.map (CommRingCat.ofHom (awMap ψ.hom g g' hg)) ≫ (opIso g U hU).inv := by
  refine (cancel_mono U.ι).1 ?_
  rw [Category.assoc, Category.assoc, opIso_inv, Scheme.Hom.resLE_comp_ι, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    awMap_alg, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc, opIso_hom]
  rfl

theorem awMap_eq {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (g : R) (g' : S) (hg : ψ g = g') (x : R) :
    awMap ψ g g' hg (algebraMap R _ x) = algebraMap S _ (ψ x) := by
  simp [awMap]

theorem awMap_mk' {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (g : R) (g' : S) (hg : ψ g = g') (x : R)
    (y : Submonoid.powers g) :
    awMap ψ g g' hg (IsLocalization.mk' _ x y) = IsLocalization.mk' (Localization.Away g') (ψ x)
      (⟨ψ y, by obtain ⟨n, hn⟩ := y.2; exact ⟨n, by rw [← hn, map_pow, hg]⟩⟩ : Submonoid.powers g') := by
  simp only [awMap, IsLocalization.map_mk']

theorem awMap_ext {R S : Type} [CommRing R] [CommRing S] (g : R) {u v : Localization.Away g →+* S}
    (h : ∀ x, u (algebraMap R _ x) = v (algebraMap R _ x)) : u = v :=
  IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext h)

section
variable {A B : Type} [CommRing A] [CommRing B] (f : A) {J : Type} [SmallCategory J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)

theorem ocb_s_nat {j k : J} (g : j ⟶ k) : (D.map g).hom ((s.app j).hom f) = (s.app k).hom f := by
  have := s.naturality g
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
  rw [this]; rfl

def locD : J ⥤ CommRingCat.{0} where
  obj j := CommRingCat.of (Localization.Away ((s.app j).hom f))
  map {j k} g := CommRingCat.ofHom (awMap (D.map g).hom ((s.app j).hom f) ((s.app k).hom f) (ocb_s_nat f D s g))
  map_id j := by
    ext1; apply awMap_ext; intro x
    simp [awMap_eq]
  map_comp {j k l} g h := by
    ext1; apply awMap_ext; intro x
    simp [awMap_eq]

variable (φ : A →+* B) (t : D ⟶ (Functor.const J).obj (CommRingCat.of B))
  (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ)

include he in
theorem t_eq (j : J) (a : A) : (t.app j).hom ((s.app j).hom a) = φ a := by
  rw [← CommRingCat.comp_apply, he j]; rfl

def locT : locD f D s ⟶ (Functor.const J).obj (CommRingCat.of (Localization.Away (φ f))) where
  app j := CommRingCat.ofHom (awMap (t.app j).hom ((s.app j).hom f) (φ f) (t_eq D s φ t he j f))
  naturality {j k} g := by
    ext1; apply awMap_ext; intro x
    simp only [locD, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, CommRingCat.hom_comp,
      CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, awMap_eq]
    rw [← CommRingCat.comp_apply, t.naturality g]; simp

end

section
variable {A B : Type} [CommRing A] [CommRing B] (f : A) {J : Type} [SmallCategory J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (φ : A →+* B) (t : D ⟶ (Functor.const J).obj (CommRingCat.of B))
  (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ)

theorem locT_app (j : J) (c : Localization.Away ((s.app j).hom f)) :
    (locT f D s φ t he).app j c = awMap (t.app j).hom _ _ (t_eq D s φ t he j f) c := rfl

omit [CommRing B] in
theorem locD_map {j k : J} (g : j ⟶ k) (c : Localization.Away ((s.app j).hom f)) :
    (locD f D s).map g c = awMap (D.map g).hom _ _ (ocb_s_nat f D s g) c := rfl

theorem locT_zero [IsFiltered J] (hc : IsColimit (Cocone.mk _ t)) (j : J)
    (c : Localization.Away ((s.app j).hom f)) (hc0 : (locT f D s φ t he).app j c = 0) :
    ∃ (k : J) (g : j ⟶ k), (locD f D s).map g c = 0 := by
  have hc' := isColimitOfPreserves (forget CommRingCat) hc
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers ((s.app j).hom f)) c
  rw [locT_app, awMap_mk'] at hc0
  obtain ⟨⟨_, p, rfl⟩, hp⟩ := (IsLocalization.mk'_eq_zero_iff (R := B) (M := Submonoid.powers (φ f)) (S := Localization.Away (φ f)) _ _).1 hc0
  have h1 : (t.app j).hom ((s.app j).hom f ^ p * x) = (t.app j).hom 0 := by
    rw [map_mul, map_pow, t_eq D s φ t he, map_zero]; exact hp
  obtain ⟨k, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' _ _).1 h1
  refine ⟨k, g, ?_⟩
  rw [locD_map, awMap_mk']
  refine (IsLocalization.mk'_eq_zero_iff (S := Localization.Away ((s.app k).hom f)) _ _).2 ⟨⟨_, pow_mem (Submonoid.mem_powers _) p⟩, ?_⟩
  change (D.map g).hom ((s.app j).hom f ^ p * x) = (D.map g).hom 0 at hg
  rw [map_mul, map_pow, ocb_s_nat f D s g] at hg
  simpa using hg

theorem locT_isColimit [IsFiltered J] (hc : IsColimit (Cocone.mk _ t)) :
    Nonempty (IsColimit (Cocone.mk _ (locT f D s φ t he))) := by
  have hc' := isColimitOfPreserves (forget CommRingCat) hc
  haveI : ReflectsColimitsOfShape J (forget CommRingCat.{0}) := reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)⟩
  · intro (z : Localization.Away (φ f))
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (φ f)) z
    obtain ⟨j, x', hx'⟩ := Types.jointly_surjective_of_isColimit hc' x
    change (t.app j).hom x' = x at hx'
    refine ⟨j, IsLocalization.mk' (Localization.Away ((s.app j).hom f)) x' (⟨_, pow_mem (Submonoid.mem_powers _) n⟩ : Submonoid.powers ((s.app j).hom f)), ?_⟩
    change _ = (locT f D s φ t he).app j _
    rw [locT_app, awMap_mk']
    subst hx'
    show IsLocalization.mk' (R := B) (M := Submonoid.powers (φ f)) (Localization.Away (φ f)) ((t.app j).hom x') _ = _
    congr 1
    apply Subtype.ext; simp [t_eq D s φ t he]
  · intro j a b hab
    have hab' : (locT f D s φ t he).app j (a - b) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hab
    obtain ⟨k, g, hg⟩ := locT_zero f D s φ t he hc j _ hab'
    refine ⟨k, g, ?_⟩
    change (locD f D s).map g a = (locD f D s).map g b
    rw [map_sub, sub_eq_zero] at hg; exact hg

end

theorem off_span_map {R S : CommRingCat.{0}} (ψ : R ⟶ S) (f : R) :
    off S ((Ideal.span {f}).map ψ.hom) = PrimeSpectrum.basicOpen (ψ.hom f) := by
  rw [Ideal.map_span, Set.image_singleton]
  exact TopologicalSpace.Opens.ext (off_span_singleton S (ψ.hom f))

theorem pull_sq (q : ℕ) (n i : ℤ) {R S : CommRingCat.{0}} (ψ : R ⟶ S) (g : R) (g' : S) (hg : ψ.hom g = g')
    (U : (Spec R).Opens) (hU : U = PrimeSpectrum.basicOpen g)
    (U' : (Spec S).Opens) (hU' : U' = PrimeSpectrum.basicOpen g')
    (h : U' ≤ Spec.map ψ ⁻¹ᵁ U) (y : Ht q (sch.obj U.toScheme) n i) :
    pull _ (opnMap (Spec.map ψ) U' U h).left (tw q i) n y =
      pull _ (sch.map (opIso g' U' hU').hom) _ _ (pull _ (sch.map (Spec.map (CommRingCat.ofHom (awMap ψ.hom g g' hg))))
        _ _ (pull _ (sch.map (opIso g U hU).inv) _ _ y)) := by
  change pull _ (sch.map ((Spec.map ψ).resLE U U' h)) _ _ y = _
  rw [opIso_sq ψ g g' hg U hU U' hU' h, Functor.map_comp, Functor.map_comp, pull_comp, pull_comp]

theorem pull_hom_inv (q : ℕ) (n i : ℤ) {X Y : Scheme.{0}} (e : X ≅ Y) (y : Ht q (sch.obj X) n i) :
    pull _ (sch.map e.hom) (tw q i) n (pull _ (sch.map e.inv) (tw q i) n y) = y := by
  rw [← pull_comp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]

theorem pull_inv_hom (q : ℕ) (n i : ℤ) {X Y : Scheme.{0}} (e : X ≅ Y) (y : Ht q (sch.obj Y) n i) :
    pull _ (sch.map e.inv) (tw q i) n (pull _ (sch.map e.hom) (tw q i) n y) = y := by
  rw [← pull_comp, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]

theorem pull_sq' (q : ℕ) (n i : ℤ) {R S : CommRingCat.{0}} (ψ : R ⟶ S) (g : R) (g' : S) (hg : ψ.hom g = g')
    (U : (Spec R).Opens) (hU : U = PrimeSpectrum.basicOpen g)
    (U' : (Spec S).Opens) (hU' : U' = PrimeSpectrum.basicOpen g')
    (h : U' ≤ Spec.map ψ ⁻¹ᵁ U) (y : Ht q (sch.obj (Spec (CommRingCat.of (Localization.Away g)))) n i) :
    pull _ (opnMap (Spec.map ψ) U' U h).left (tw q i) n (pull _ (sch.map (opIso g U hU).hom) _ _ y) =
      pull _ (sch.map (opIso g' U' hU').hom) _ _ (pull _ (sch.map (Spec.map (CommRingCat.ofHom (awMap ψ.hom g g' hg))))
        _ _ y) := by
  rw [pull_sq q n i ψ g g' hg U hU U' hU' h, pull_inv_hom]

theorem pull_hom_zero (q : ℕ) (n i : ℤ) {X Y : Scheme.{0}} (e : X ≅ Y) (y : Ht q (sch.obj Y) n i)
    (hy : pull _ (sch.map e.hom) (tw q i) n y = 0) : y = 0 := by
  rw [← pull_inv_hom q n i e y, hy, map_zero]

theorem offContBasic_of : OffContBasic := by
  intro a1 a4 b1 q A B _ _ φ f hq J _ _ D s t hc he n i
  obtain ⟨hc2⟩ := locT_isColimit f D s φ t he hc
  have hqB : IsUnit (q : Localization.Away (φ f)) := by
    have := (hq.map ((algebraMap B (Localization.Away (φ f))).comp φ)); simpa using this
  have hqj : ∀ j, IsUnit (q : (locD f D s).obj j) := fun j => by
    have := (hq.map ((algebraMap _ (Localization.Away ((s.app j).hom f))).comp (s.app j).hom))
    exact (by simpa using this : IsUnit ((q : ℕ) : Localization.Away ((s.app j).hom f)))
  obtain ⟨hS, hI⟩ := spec_cont b1 q (locD f D s) (locT f D s φ t he) hc2 hqB hqj n i
  have hUB : off B ((Ideal.span {f}).map φ) = PrimeSpectrum.basicOpen (φ f) :=
    off_span_map (R := CommRingCat.of A) (S := CommRingCat.of B) (CommRingCat.ofHom φ) f
  have hUj : ∀ j, off (D.obj j) ((Ideal.span {f}).map (s.app j).hom) = PrimeSpectrum.basicOpen ((s.app j).hom f) :=
    fun j => off_span_map (R := CommRingCat.of A) (s.app j) f
  have hB : ∀ j, off B ((Ideal.span {f}).map φ) ≤ Spec.map (t.app j) ⁻¹ᵁ off (D.obj j) ((Ideal.span {f}).map (s.app j).hom) := fun j => by
    intro x hx
    have e := off_map (t.app j).hom ((Ideal.span {f}).map (s.app j).hom)
    simp only [CommRingCat.ofHom_hom] at e
    rw [← e, Ideal.map_map]
    have : (t.app j).hom.comp (s.app j).hom = φ := by
      rw [← CommRingCat.hom_comp, he j]; rfl
    rw [this]; exact hx
  have hD : ∀ {j k : J} (g : j ⟶ k), off (D.obj k) ((Ideal.span {f}).map (s.app k).hom) ≤
      Spec.map (D.map g) ⁻¹ᵁ off (D.obj j) ((Ideal.span {f}).map (s.app j).hom) := fun {j k} g => by
    intro x hx
    have e := off_map (D.map g).hom ((Ideal.span {f}).map (s.app j).hom)
    simp only [CommRingCat.ofHom_hom] at e
    rw [← e, Ideal.map_map]
    have : (D.map g).hom.comp (s.app j).hom = (s.app k).hom := by
      have := s.naturality g
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
      rw [this]; rfl
    rw [this]; exact hx
  constructor
  · intro x
    obtain ⟨j, y', hy'⟩ := hS (pull (ZMod q) (sch.map (opIso (R := CommRingCat.of B) (φ f) (off B ((Ideal.span {f}).map φ)) hUB).inv) (tw q i) n x)
    refine ⟨j, hB j, pull _ (sch.map (opIso (R := D.obj j) ((s.app j).hom f) (off (D.obj j) ((Ideal.span {f}).map (s.app j).hom)) (hUj j)).hom) _ _ y', ?_⟩
    exact (pull_sq' q n i (t.app j) ((s.app j).hom f) (φ f) (t_eq D s φ t he j f) _ (hUj j) _ hUB (hB j) y').trans
      ((congrArg (pull _ (sch.map (opIso (R := CommRingCat.of B) (φ f) (off B ((Ideal.span {f}).map φ)) hUB).hom) (tw q i) n) hy').trans
        (pull_hom_inv q n i _ x))
  · intro j h y hy
    replace hy := (pull_sq q n i (t.app j) ((s.app j).hom f) (φ f) (t_eq D s φ t he j f) _ (hUj j) _ hUB h y).symm.trans hy
    have hy2 := pull_hom_zero q n i _ _ hy
    obtain ⟨k, g, hk⟩ := hI j _ hy2
    refine ⟨k, g, hD g, ?_⟩
    exact (pull_sq q n i (D.map g) ((s.app j).hom f) ((s.app k).hom f) (ocb_s_nat f D s g) _ (hUj j) _ (hUj k) (hD g) y).trans
      ((congrArg (pull _ (sch.map (opIso (R := D.obj k) ((s.app k).hom f) (off (D.obj k) ((Ideal.span {f}).map (s.app k).hom)) (hUj k)).hom) (tw q i) n) hk).trans
        (map_zero _))

end LateralTheory.CohomologicalPurity
