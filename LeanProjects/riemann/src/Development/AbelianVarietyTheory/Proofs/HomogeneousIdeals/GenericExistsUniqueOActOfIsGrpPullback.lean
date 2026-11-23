import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

universe u

namespace GlobalTheory.StalkLimit

open TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

theorem exists_lift_fromSpecStalk {S T : Scheme.{u}} (x : S) (t : T ⟶ S)
    (ht : ∀ V : S.Opens, x ∈ V → ⊤ ≤ t ⁻¹ᵁ V) :
    ∃ l : T ⟶ Spec (S.presheaf.stalk x), l ≫ S.fromSpecStalk x = t := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hU' : IsAffineOpen U := hU
  have htop : (⊤ : T.Opens) ≤ t ⁻¹ᵁ U := ht U hxU
  have unit_of_top : ∀ s : Γ(T, ⊤), T.basicOpen s = ⊤ → IsUnit s := by
    intro s hs
    have h1 := (T.toRingedSpace.isUnit_res_basicOpen s).map (T.presheaf.map (homOfLE hs.ge).op).hom
    convert h1 using 1
    change s = (T.presheaf.map _ ≫ T.presheaf.map _).hom s
    rw [← Functor.map_comp, Subsingleton.elim (_ ≫ _) (𝟙 _), CategoryTheory.Functor.map_id]
    rfl
  let _ := (S.presheaf.germ U x hxU).hom.toAlgebra
  have := hU'.isLocalization_stalk ⟨x, hxU⟩
  have hunit : ∀ y : (hU'.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl,
      IsUnit ((t.appLE U ⊤ htop).hom y) := by
    intro y
    have h1 : IsUnit (S.presheaf.germ U x hxU y) := IsLocalization.map_units (S.presheaf.stalk x) y
    have h2 : x ∈ S.basicOpen (y : Γ(S, U)) := (S.mem_basicOpen' (U := U) (y : Γ(S, U)) ⟨x, hxU⟩).mpr h1
    apply unit_of_top
    rw [Scheme.basicOpen_appLE]
    exact top_le_iff.mp (le_inf le_rfl (ht _ h2))
  let χ := IsLocalization.lift (M := (hU'.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl)
    (S := S.presheaf.stalk x) (g := (t.appLE U ⊤ htop).hom) hunit
  have hχ : S.presheaf.germ U x hxU ≫ CommRingCat.ofHom χ = t.appLE U ⊤ htop := by
    ext1
    exact IsLocalization.lift_comp _
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom χ), ?_⟩
  have hfac : T.toSpecΓ ≫ Spec.map (t.appLE U ⊤ htop) ≫ hU'.fromSpec = t := by
    have e1 := Scheme.Opens.toSpecΓ_SpecMap_appLE t U ⊤ htop
    rw [Scheme.Opens.toSpecΓ_top, Category.assoc] at e1
    have : IsIso (⊤ : T.Opens).ι := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
    rw [← cancel_epi (⊤ : T.Opens).ι, reassoc_of% e1, hU'.toSpecΓ_fromSpec,
      Scheme.Hom.resLE_comp_ι]
  rw [← hU'.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk, Category.assoc,
    ← Spec.map_comp_assoc, hχ, hfac]

abbrev AffNhd {S : Scheme.{u}} (x : S) : Type u := {V : S.Opens // x ∈ V ∧ IsAffineOpen V}

instance {S : Scheme.{u}} (x : S) : IsCofiltered (AffNhd x) := by
  have : Nonempty (AffNhd x) := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    exact ⟨U, hxU, hU⟩
  have : IsDirected (AffNhd x) (· ≥ ·) := ⟨fun V W => by
    obtain ⟨U, h₁, h₂, h₃ : U ≤ V.1 ⊓ W.1⟩ :=
      Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens (show x ∈ V.1 ⊓ W.1 from ⟨V.2.1, W.2.1⟩)
    exact ⟨⟨U, h₂, h₁⟩, h₃.trans inf_le_left, h₃.trans inf_le_right⟩⟩
  infer_instance

variable {S X : Scheme.{u}} (x : S) (p : X ⟶ S)

def diagram : AffNhd x ⥤ Scheme.{u} where
  obj V := pullback p V.1.ι
  map {V W} i := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ S.homOfLE i.le) (by
    rw [Category.assoc, Scheme.homOfLE_ι, pullback.condition])
  map_id V := by
    rw [← cancel_mono (pullback.fst p V.1.ι), pullback.lift_fst, Category.id_comp]
  map_comp {U V W} i j := by
    rw [← cancel_mono (pullback.fst p W.1.ι), pullback.lift_fst, Category.assoc, pullback.lift_fst,
      pullback.lift_fst]

theorem diagram_map_fst {V W : AffNhd x} (i : V ⟶ W) :
    (diagram x p).map i ≫ pullback.fst p W.1.ι = pullback.fst p V.1.ι := by
  dsimp only [diagram]
  exact pullback.lift_fst _ _ _

instance {V W : AffNhd x} (i : V ⟶ W) : IsAffineHom ((diagram x p).map i) := by
  have h : IsPullback ((diagram x p).map i) (pullback.snd p V.1.ι) (pullback.snd p W.1.ι) (S.homOfLE i.le) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p W.1.ι)
    rw [diagram_map_fst, Scheme.homOfLE_ι]
    exact IsPullback.of_hasPullback _ _
  have : IsAffine V.1.toScheme := V.2.2
  have : IsAffine W.1.toScheme := W.2.2
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance

variable {x p} {X' : Scheme.{u}} {φ : X' ⟶ X} {p' : X' ⟶ Spec (S.presheaf.stalk x)}

def cone (h : IsPullback φ p' p (S.fromSpecStalk x)) : Cone (diagram x p) where
  pt := X'
  π := { app V := pullback.lift φ (p' ≫ V.1.fromSpecStalkOfMem x V.2.1) (by
          rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, h.w])
         naturality V W i := by
          refine (cancel_mono (pullback.fst p W.1.ι)).1 ?_
          simp only [Category.assoc, diagram_map_fst, pullback.lift_fst]
          exact Category.id_comp _ }

theorem cone_π_fst (h : IsPullback φ p' p (S.fromSpecStalk x)) (V : AffNhd x) :
    (cone h).π.app V ≫ pullback.fst p V.1.ι = φ := by
  dsimp only [cone]
  exact pullback.lift_fst _ _ _

theorem nonempty_isLimit (h : IsPullback φ p' p (S.fromSpecStalk x)) : Nonempty (IsLimit (cone h)) := by
  obtain ⟨V0⟩ : Nonempty (AffNhd x) := IsCofiltered.nonempty
  have hfst : ∀ (s : Cone (diagram x p)) (V W : AffNhd x),
      s.π.app V ≫ pullback.fst p V.1.ι = s.π.app W ≫ pullback.fst p W.1.ι := by
    intro s V W
    rw [← s.w (IsCofiltered.minToLeft V W), ← s.w (IsCofiltered.minToRight V W), Category.assoc,
      Category.assoc, diagram_map_fst, diagram_map_fst]
  have hin : ∀ (s : Cone (diagram x p)) (W : S.Opens), x ∈ W →
      ⊤ ≤ (s.π.app V0 ≫ pullback.fst p V0.1.ι ≫ p) ⁻¹ᵁ W := by
    intro s W hxW z _
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
    have e : s.π.app V0 ≫ pullback.fst p V0.1.ι ≫ p =
        (s.π.app ⟨V, hxV, hV⟩ ≫ pullback.snd p (Scheme.Opens.ι V)) ≫ Scheme.Opens.ι V := by
      rw [← Category.assoc, hfst s V0 ⟨V, hxV, hV⟩, Category.assoc, Category.assoc,
        pullback.condition]
    change (s.π.app V0 ≫ pullback.fst p V0.1.ι ≫ p) z ∈ W
    rw [e, Scheme.Hom.comp_apply]
    exact hVW (Scheme.Opens.range_ι V ▸ Set.mem_range_self _)
  let L : ∀ s : Cone (diagram x p), s.pt ⟶ X' := fun s =>
    h.lift (s.π.app V0 ≫ pullback.fst p V0.1.ι) (exists_lift_fromSpecStalk x _ (hin s)).choose
      (by rw [(exists_lift_fromSpecStalk x _ (hin s)).choose_spec, Category.assoc])
  refine ⟨⟨L, fun s V => ?_, fun s m hm => ?_⟩⟩
  · dsimp only [L]
    apply pullback.hom_ext
    · rw [Category.assoc, cone_π_fst, h.lift_fst]
      exact hfst s V0 V
    · rw [← cancel_mono V.1.ι]
      simp only [Category.assoc, cone, pullback.lift_snd_assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
        h.lift_snd_assoc, (exists_lift_fromSpecStalk x _ (hin s)).choose_spec]
      rw [← pullback.condition]
      simp only [← Category.assoc, hfst s V0 V]
  · have e1 : m ≫ φ = s.π.app V0 ≫ pullback.fst p V0.1.ι := by
      rw [← hm V0, Category.assoc, cone_π_fst]
    dsimp only [L]
    apply h.hom_ext
    · rw [e1, h.lift_fst]
    · rw [← cancel_mono (S.fromSpecStalk x)]
      simp only [Category.assoc, ← h.w, reassoc_of% e1, h.lift_fst_assoc]

theorem exists_spread [QuasiCompact p] [QuasiSeparated p] (h : IsPullback φ p' p (S.fromSpecStalk x))
    {Y : Scheme.{u}} (q : Y ⟶ S) [LocallyOfFinitePresentation q] (a : X' ⟶ Y) (ha : a ≫ q = φ ≫ p) :
    ∃ (V : S.Opens) (_ : x ∈ V) (_ : IsAffineOpen V) (w : X' ⟶ pullback p V.ι) (g : pullback p V.ι ⟶ Y),
      w ≫ pullback.fst p V.ι = φ ∧ w ≫ g = a ∧ g ≫ q = pullback.fst p V.ι ≫ p := by
  obtain ⟨hc⟩ := nonempty_isLimit h
  have hcpt : ∀ V : AffNhd x, CompactSpace ((diagram x p).obj V) := fun V => by
    have : IsAffine V.1.toScheme := V.2.2
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V.1.ι)
  have hqs : ∀ V : AffNhd x, QuasiSeparatedSpace ((diagram x p).obj V) := fun V => by
    have : IsAffine V.1.toScheme := V.2.2
    exact (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd p V.1.ι)).mp inferInstance
  let t : diagram x p ⟶ (Functor.const (AffNhd x)).obj S :=
    { app := fun V => pullback.fst p V.1.ι ≫ p
      naturality := fun V W i => by
        dsimp
        rw [Category.comp_id, ← Category.assoc, diagram_map_fst] }
  have ht : (cone h).π ≫ t = (Functor.const _).map (a ≫ q) := by
    apply NatTrans.ext
    funext V
    simp only [NatTrans.comp_app, Functor.const_map_app, t]
    rw [← Category.assoc, cone_π_fst, ha]
  obtain ⟨V, g, hg₁, hg₂⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (diagram x p) t q (cone h) hc a ht
  exact ⟨V.1, V.2.1, V.2.2, (cone h).π.app V, g, cone_π_fst h V, hg₁, hg₂⟩

end GlobalTheory.StalkLimit

namespace GlobalTheory

open ExtUnique

def IsGenericPointHom {U S : Scheme.{u}} [IsIntegral S] (j : U ⟶ S) : Prop :=
  ∃ e : U ≅ Spec (S.presheaf.stalk (genericPoint S)), e.hom ≫ S.fromSpecStalk (genericPoint S) = j

namespace IsGenericPointHom

theorem fromSpecStalk (S : Scheme.{u}) [IsIntegral S] : IsGenericPointHom (S.fromSpecStalk (genericPoint S)) :=
  ⟨Iso.refl _, Category.id_comp _⟩

theorem of_isPreimmersion {S : Scheme.{u}} [IsIntegral S] {K : Type u} [Field K] (j : Spec (.of K) ⟶ S)
    [IsPreimmersion j] [IsDominant j] : IsGenericPointHom j := by
  have hx : j (IsLocalRing.closedPoint K) = genericPoint S := by
    have hr : Set.range j = {j (IsLocalRing.closedPoint K)} := by
      ext y
      constructor
      · rintro ⟨u, rfl⟩
        rw [Subsingleton.elim u (IsLocalRing.closedPoint K)]
        rfl
      · rintro rfl
        exact ⟨_, rfl⟩
    have hg : IsGenericPoint (j (IsLocalRing.closedPoint K)) ⊤ := by
      show closure _ = Set.univ
      rw [← hr]
      exact j.denseRange.closure_range
    exact hg.eq (genericPoint_spec S)
  have hfield : IsField ↑(S.presheaf.stalk (j (IsLocalRing.closedPoint K))) := by
    rw [hx]
    exact Field.toIsField S.functionField
  let := hfield.toField
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo j) := by
    simp only [Scheme.stalkClosedPointTo, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (stalkClosedPointIso _).commRingCatIsoToRingEquiv.surjective.comp
      (j.stalkMap_surjective _)
  have hinj : Function.Injective (Scheme.stalkClosedPointTo j) :=
    (Scheme.stalkClosedPointTo j).hom.injective
  have : IsIso (Scheme.stalkClosedPointTo j) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  unfold IsGenericPointHom
  rw [← hx]
  exact ⟨asIso (Spec.map (Scheme.stalkClosedPointTo j)), Scheme.Spec_stalkClosedPointTo_fromSpecStalk j⟩

theorem fractionField (R K : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :
    IsGenericPointHom (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    rw [isDominant_iff]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
    intro r hr
    have h0 : algebraMap R K r = 0 := hr
    rw [IsFractionRing.to_map_eq_zero_iff] at h0
    rw [h0]
    exact zero_mem _
  exact of_isPreimmersion _

variable {U S : Scheme.{u}} [IsIntegral S] {j : U ⟶ S}

theorem range_eq (hj : IsGenericPointHom j) : Set.range j = {genericPoint S} := by
  obtain ⟨e, rfl⟩ := hj
  have hgen : ∀ y : S, y ⤳ genericPoint S → y = genericPoint S := fun y hy =>
    (hy.antisymm ((genericPoint_spec S).specializes trivial)).eq
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, rfl⟩
    apply hgen
    have hy : (e.hom ≫ S.fromSpecStalk (genericPoint S)) u ∈ Set.range (S.fromSpecStalk (genericPoint S)) :=
      ⟨e.hom u, by simp⟩
    rwa [Scheme.range_fromSpecStalk] at hy
  · rintro rfl
    have hη : genericPoint S ∈ Set.range (S.fromSpecStalk (genericPoint S)) := by
      rw [Scheme.range_fromSpecStalk]
      exact specializes_rfl
    obtain ⟨u, hu⟩ := hη
    exact ⟨e.inv u, by simp [hu]⟩

theorem isAffine (hj : IsGenericPointHom j) : IsAffine U := by
  obtain ⟨e, -⟩ := hj
  exact IsAffine.of_isIso e.hom

theorem quasiCompact_and_dominant_of_comp [IsLocallyNoetherian S] {V : Scheme.{u}} {k : U ⟶ V} {i : V ⟶ S}
    [IsOpenImmersion i] (hj : IsGenericPointHom (k ≫ i)) :
    QuasiCompact k ∧ IsSchemeTheoreticallyDominant k := by
  have : IsAffine U := hj.isAffine
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion i
  have : IsReduced V := isReduced_of_isOpenImmersion i
  have hdom : IsDominant k := by
    rw [isDominant_iff, DenseRange, i.isOpenEmbedding.isInducing.dense_iff]
    intro v
    have hr : i '' Set.range k = {genericPoint S} := by
      rw [← hj.range_eq, ← Set.range_comp]
      rfl
    have hη : closure {genericPoint S} = (⊤ : Set S) := genericPoint_spec S
    rw [hr, hη]
    trivial
  exact ⟨inferInstance, IsSchemeTheoreticallyDominant.of_isDominant k⟩

theorem quasiCompact_and_dominant [IsLocallyNoetherian S] (hj : IsGenericPointHom j) :
    QuasiCompact j ∧ IsSchemeTheoreticallyDominant j :=
  quasiCompact_and_dominant_of_comp (i := 𝟙 S) (by rwa [Category.comp_id])

private lemma hom_ext_lemma {W X Y Z : Scheme.{u}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (hs : f ≫ s = g ≫ s) (w : W ⟶ X) [IsSchemeTheoreticallyDominant w] (hw : w ≫ f = w ≫ g) : f = g := by
  let e := pullback.fst (pullback.lift f g hs) (pullback.diagonal s)
  let k : W ⟶ pullback (pullback.lift f g hs) (pullback.diagonal s) :=
    pullback.lift w (w ≫ f) (by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hw])
  have hk : k ≫ e = w := pullback.lift_fst _ _ _
  have hker : e.ker = ⊥ := by
    refine le_bot_iff.mp ((Scheme.Hom.le_ker_comp k e).trans ?_)
    rw [hk, w.ker_eq_bot]
  have : IsIso e := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  have hc := pullback.condition (f := pullback.lift f g hs) (g := pullback.diagonal s)
  have h₁ : e ≫ f = pullback.snd _ _ := by
    calc e ≫ f = e ≫ pullback.lift f g hs ≫ pullback.fst s s := by rw [pullback.lift_fst]
      _ = pullback.snd _ _ ≫ pullback.diagonal s ≫ pullback.fst s s := by rw [reassoc_of% hc]
      _ = pullback.snd _ _ := by simp
  have h₂ : e ≫ g = pullback.snd _ _ := by
    calc e ≫ g = e ≫ pullback.lift f g hs ≫ pullback.snd s s := by rw [pullback.lift_snd]
      _ = pullback.snd _ _ ≫ pullback.diagonal s ≫ pullback.snd s s := by rw [reassoc_of% hc]
      _ = pullback.snd _ _ := by simp
  exact (cancel_epi e).mp (h₁.trans h₂.symm)

private theorem isGrpPullback_pullback_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    IsGrpPullback ((Over.pullback f).obj G) G f (pullback.fst G.hom f) := by
  refine ⟨IsPullback.of_hasPullback _ _, ?_⟩
  intro T x y x₀ y₀ hx hy
  have e : ∀ {A B : Over S} (g : A ⟶ B),
      ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left := by
    intro A B g
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have key : (lift x₀ y₀).left =
      (lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫ pullback.fst (G ⊗ G).hom f := by
    apply pullback.hom_ext
    · calc (lift x₀ y₀).left ≫ pullback.fst G.hom G.hom = (lift x₀ y₀ ≫ fst G G).left := rfl
        _ = x.left ≫ pullback.fst G.hom f := by rw [lift_fst, hx]
        _ = (lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G ≫ (Over.pullback f).map (fst G G)).left ≫
              pullback.fst G.hom f := by
          rw [Functor.Monoidal.μ_fst, lift_fst]
        _ = _ := by simp only [Over.comp_left, Category.assoc, e]; rfl
    · calc (lift x₀ y₀).left ≫ pullback.snd G.hom G.hom = (lift x₀ y₀ ≫ snd G G).left := rfl
        _ = y.left ≫ pullback.fst G.hom f := by rw [lift_snd, hy]
        _ = (lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G ≫ (Over.pullback f).map (snd G G)).left ≫
              pullback.fst G.hom f := by
          rw [Functor.Monoidal.μ_snd, lift_snd]
        _ = _ := by simp only [Over.comp_left, Category.assoc, e]; rfl
  change (lift x₀ y₀ ≫ μ).left =
    (lift x y ≫ (Functor.LaxMonoidal.μ (Over.pullback f) G G ≫ (Over.pullback f).map μ)).left ≫ pullback.fst G.hom f
  rw [Over.comp_left, key]
  simp only [Over.comp_left, Category.assoc, e]

end IsGenericPointHom

theorem spread_hom_generic_of_isGrpPullback {U S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] {j : U ⟶ S}
    (hj : IsGenericPointHom j) {G H : Over S} [GrpObj G] [GrpObj H] [Flat G.hom] [QuasiCompact G.hom]
    [QuasiSeparated G.hom] [IsSeparated H.hom] [LocallyOfFinitePresentation H.hom] {G' H' : Over U} [GrpObj G']
    [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G j φ)
    (hψ : IsGrpPullback H' H j ψ) (f : G' ⟶ H') [IsMonHom f] :
    ∃ (V : S.Opens) (_ : genericPoint S ∈ V) (_ : IsAffineOpen V)
      (g : (Over.pullback V.ι).obj G ⟶ (Over.pullback V.ι).obj H) (_ : IsMonHom g)
      (w : G'.left ⟶ ((Over.pullback V.ι).obj G).left),
      w ≫ pullback.fst G.hom V.ι = φ ∧ w ≫ g.left ≫ pullback.fst H.hom V.ι = f.left ≫ ψ := by
  obtain ⟨e, he⟩ := hj
  have hsq : IsPullback j e.hom (𝟙 S) (S.fromSpecStalk (genericPoint S)) :=
    IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, he]⟩
  have hpb := hφ.1.paste_vert hsq
  rw [Category.comp_id] at hpb
  have ha : (f.left ≫ ψ) ≫ H.hom = φ ≫ G.hom := by
    rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w f, hφ.1.w]
  obtain ⟨V, hηV, hVa, w, g₀, hw, hwg, hg₀⟩ := StalkLimit.exists_spread hpb H.hom (f.left ≫ ψ) ha
  let g : (Over.pullback V.ι).obj G ⟶ (Over.pullback V.ι).obj H :=
    Over.homMk (pullback.lift g₀ (pullback.snd G.hom V.ι) (by rw [hg₀, pullback.condition]))
      (pullback.lift_snd _ _ _)
  have hgl : g.left ≫ pullback.fst H.hom V.ι = g₀ := pullback.lift_fst _ _ _
  have hmon : IsMonHom g := by
    obtain ⟨k, hk⟩ : ∃ k : U ⟶ V, k ≫ V.ι = j := by
      refine ⟨IsOpenImmersion.lift V.ι j ?_, IsOpenImmersion.lift_fac _ _ _⟩
      rintro _ ⟨u, rfl⟩
      have hr : j u ∈ Set.range j := ⟨u, rfl⟩
      rw [IsGenericPointHom.range_eq ⟨e, he⟩, Set.mem_singleton_iff] at hr
      rw [Scheme.Opens.range_ι]
      exact hr ▸ hηV
    subst hk
    obtain ⟨_, _⟩ := IsGenericPointHom.quasiCompact_and_dominant_of_comp (k := k) (i := V.ι) ⟨e, he⟩
    have hwk : w ≫ pullback.snd G.hom V.ι = G'.hom ≫ k := by
      rw [← cancel_mono V.ι, Category.assoc, ← pullback.condition, ← Category.assoc, hw, hφ.1.w,
        Category.assoc]
    have hsqV : IsPullback w G'.hom (pullback.snd G.hom V.ι) k :=
      IsPullback.of_right (by rw [hw]; exact hφ.1) hwk (IsPullback.of_hasPullback G.hom V.ι)
    have hG'V2 : ∀ (T : Over U) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ k) ⟶ (Over.pullback V.ι).obj G),
        x₀.left = x.left ≫ w → y₀.left = y.left ≫ w → (x₀ * y₀).left = (x * y).left ≫ w := by
      intro T x y x₀ y₀ hx hy
      let E : Over.mk (T.hom ≫ (k ≫ V.ι)) ≅ Over.mk ((T.hom ≫ k) ≫ V.ι) :=
        Over.isoMk (Iso.refl _) (by simp)
      let x₁ : Over.mk ((T.hom ≫ k) ≫ V.ι) ⟶ G := Over.homMk (x₀.left ≫ pullback.fst G.hom V.ι) (by
        rw [Category.assoc x₀.left, pullback.condition, ← Category.assoc x₀.left]
        exact congr_arg (· ≫ V.ι) (Over.w x₀))
      let y₁ : Over.mk ((T.hom ≫ k) ≫ V.ι) ⟶ G := Over.homMk (y₀.left ≫ pullback.fst G.hom V.ι) (by
        rw [Category.assoc y₀.left, pullback.condition, ← Category.assoc y₀.left]
        exact congr_arg (· ≫ V.ι) (Over.w y₀))
      have hC : (x₁ * y₁).left = (x₀ * y₀).left ≫ pullback.fst G.hom V.ι :=
        (IsGenericPointHom.isGrpPullback_pullback_fst V.ι G).2 (Over.mk (T.hom ≫ k)) x₀ y₀ x₁ y₁ rfl rfl
      have hB : ((E.hom ≫ x₁) * (E.hom ≫ y₁)).left = (x * y).left ≫ φ :=
        hφ.2 T x y (E.hom ≫ x₁) (E.hom ≫ y₁) (by simp [E, x₁, hx, hw]) (by simp [E, y₁, hy, hw])
      have hEc : ((E.hom ≫ x₁) * (E.hom ≫ y₁)).left = (x₁ * y₁).left := by
        rw [← MonObj.comp_mul]
        simp [E]
      apply pullback.hom_ext
      · rw [← hC, ← hEc, hB, Category.assoc, hw]
      · rw [Category.assoc, hwk, ← Category.assoc, Over.w (x * y)]
        exact Over.w (x₀ * y₀)
    have _ : Flat ((Over.pullback V.ι).obj G).hom :=
      show Flat (pullback.snd G.hom V.ι) from inferInstance
    have _ : Flat ((Over.pullback V.ι).obj G ⊗ (Over.pullback V.ι).obj G).hom :=
      show Flat (pullback.fst ((Over.pullback V.ι).obj G).hom ((Over.pullback V.ι).obj G).hom ≫
        ((Over.pullback V.ι).obj G).hom) from inferInstance
    have hsnd : ∀ {A : Over V.toScheme} (u v : A ⟶ (Over.pullback V.ι).obj H),
        u.left ≫ pullback.snd H.hom V.ι = v.left ≫ pullback.snd H.hom V.ι :=
      fun u v => (Over.w u).trans (Over.w v).symm
    have hmul : μ[(Over.pullback V.ι).obj G] ≫ g = (g ⊗ₘ g) ≫ μ[(Over.pullback V.ι).obj H] := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      swap
      · exact hsnd _ _
      let GV := (Over.pullback V.ι).obj G
      let π := pullback.fst (GV ⊗ GV).hom k
      let σ := pullback.snd (GV ⊗ GV).hom k
      let T' : Over U := Over.mk σ
      let a₁ : Over.mk (σ ≫ k) ⟶ GV := Over.homMk (π ≫ pullback.fst GV.hom GV.hom) (by
        rw [Category.assoc]
        exact pullback.condition)
      let a₂ : Over.mk (σ ≫ k) ⟶ GV := Over.homMk (π ≫ pullback.snd GV.hom GV.hom) (by
        rw [Category.assoc, ← pullback.condition (f := GV.hom) (g := GV.hom)]
        exact pullback.condition)
      have hl : (lift a₁ a₂).left = π := by
        apply pullback.hom_ext
        · exact congr_arg (fun u => u.left) (lift_fst a₁ a₂)
        · exact congr_arg (fun u => u.left) (lift_snd a₁ a₂)
      let x₁ : T' ⟶ G' := Over.homMk (hsqV.lift a₁.left σ (Over.w a₁)) (hsqV.lift_snd _ _ _)
      let x₂ : T' ⟶ G' := Over.homMk (hsqV.lift a₂.left σ (Over.w a₂)) (hsqV.lift_snd _ _ _)
      have hx₁ : x₁.left ≫ w = a₁.left := hsqV.lift_fst _ _ _
      have hx₂ : x₂.left ≫ w = a₂.left := hsqV.lift_fst _ _ _
      have hA : (a₁ * a₂).left = (x₁ * x₂).left ≫ w := hG'V2 T' x₁ x₂ a₁ a₂ hx₁.symm hx₂.symm
      let E : Over.mk (σ ≫ (k ≫ V.ι)) ≅ Over.mk ((σ ≫ k) ≫ V.ι) :=
        Over.isoMk (Iso.refl _) (by simp)
      let c₁ : Over.mk ((σ ≫ k) ≫ V.ι) ⟶ H :=
        Over.homMk ((a₁ ≫ g).left ≫ pullback.fst H.hom V.ι) (by
          rw [Category.assoc (a₁ ≫ g).left, pullback.condition, ← Category.assoc (a₁ ≫ g).left]
          exact congr_arg (· ≫ V.ι) (Over.w (a₁ ≫ g)))
      let c₂ : Over.mk ((σ ≫ k) ≫ V.ι) ⟶ H :=
        Over.homMk ((a₂ ≫ g).left ≫ pullback.fst H.hom V.ι) (by
          rw [Category.assoc (a₂ ≫ g).left, pullback.condition, ← Category.assoc (a₂ ≫ g).left]
          exact congr_arg (· ≫ V.ι) (Over.w (a₂ ≫ g)))
      have hC : (c₁ * c₂).left = ((a₁ ≫ g) * (a₂ ≫ g)).left ≫ pullback.fst H.hom V.ι :=
        (IsGenericPointHom.isGrpPullback_pullback_fst V.ι H).2 (Over.mk (σ ≫ k)) (a₁ ≫ g) (a₂ ≫ g) c₁ c₂ rfl rfl
      have hci : ∀ (a : Over.mk (σ ≫ k) ⟶ GV) (x : T' ⟶ G'), x.left ≫ w = a.left →
          (a ≫ g).left ≫ pullback.fst H.hom V.ι = (x ≫ f).left ≫ ψ := by
        intro a x hx
        rw [Over.comp_left, Category.assoc, hgl, ← hx, Category.assoc, hwg, Over.comp_left,
          Category.assoc]
      have hB : ((E.hom ≫ c₁) * (E.hom ≫ c₂)).left = ((x₁ ≫ f) * (x₂ ≫ f)).left ≫ ψ :=
        hψ.2 T' (x₁ ≫ f) (x₂ ≫ f) (E.hom ≫ c₁) (E.hom ≫ c₂)
          ((Category.id_comp _).trans (hci a₁ x₁ hx₁)) ((Category.id_comp _).trans (hci a₂ x₂ hx₂))
      have hEc : ((E.hom ≫ c₁) * (E.hom ≫ c₂)).left = (c₁ * c₂).left := by
        rw [← MonObj.comp_mul]
        simp [E]
      apply IsGenericPointHom.hom_ext_lemma H.hom (by
          rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc,
            hsnd (μ[GV] ≫ g) ((g ⊗ₘ g) ≫ μ[(Over.pullback V.ι).obj H])]) π
      rw [← hl]
      calc (lift a₁ a₂).left ≫ (μ[GV] ≫ g).left ≫ pullback.fst H.hom V.ι
          = (a₁ * a₂).left ≫ g.left ≫ pullback.fst H.hom V.ι := by
            simp only [Over.comp_left, Category.assoc, Hom.mul_def]
        _ = ((x₁ ≫ f) * (x₂ ≫ f)).left ≫ ψ := by
            rw [hA, hgl, Category.assoc, hwg, ← MonObj.mul_comp, Over.comp_left, Category.assoc]
        _ = ((a₁ ≫ g) * (a₂ ≫ g)).left ≫ pullback.fst H.hom V.ι := by rw [← hB, hEc, hC]
        _ = (lift a₁ a₂).left ≫ ((g ⊗ₘ g) ≫ μ[(Over.pullback V.ι).obj H]).left ≫
              pullback.fst H.hom V.ι := by
            simp only [Over.comp_left, Category.assoc, Hom.mul_def, ← lift_map]
    refine ⟨?_, hmul⟩
    have h1 : (1 : 𝟙_ (Over V.toScheme) ⟶ (Over.pullback V.ι).obj G) ≫ g =
        ((1 : 𝟙_ (Over V.toScheme) ⟶ (Over.pullback V.ι).obj G) ≫ g) * ((1 : 𝟙_ (Over V.toScheme) ⟶ _) ≫ g) := by
      conv_lhs => rw [← mul_one (1 : 𝟙_ (Over V.toScheme) ⟶ (Over.pullback V.ι).obj G)]
      rw [Hom.mul_def, Hom.mul_def, Category.assoc, hmul, ← Category.assoc, lift_map]
    have h2 : (1 : 𝟙_ (Over V.toScheme) ⟶ (Over.pullback V.ι).obj G) ≫ g = 1 := by
      simpa using h1.symm
    simpa [Hom.one_def] using h2
  exact ⟨V, hηV, hVa, g, hmon, w, hw, by rw [hgl, hwg]⟩

end GlobalTheory

namespace GlobalTheory.Published.SemiAbelianHomExtension

open ExtUnique

variable {S U : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] {j : U ⟶ S}

theorem generic_of_isGrpPullback (h : SemiAbelianHomExtension) (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (hj : IsGenericPointHom j) {G H : Over S} [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    {G' H' : Over U} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback H' H j ψ) (f : G' ⟶ H') [IsMonHom f] :
    ∃! F : G ⟶ H, IsMonHom F ∧ f.left ≫ ψ = φ ≫ F.left := by
  have _ : Smooth G.hom := hG.smooth
  have _ : IsSeparated G.hom := hG.separated
  have _ : QuasiCompact G.hom := hG.quasiCompact
  have _ : Smooth H.hom := hH.smooth
  have _ : IsSeparated H.hom := hH.separated
  obtain ⟨V, hηV, -, g, hg, w, hw₁, hw₂⟩ := spread_hom_generic_of_isGrpPullback hj hφ hψ f
  have hVd : Dense (V : Set S) := V.isOpen.dense ⟨_, hηV⟩
  obtain ⟨F, ⟨hF, hFg⟩, -⟩ := h S hS V hVd G H hG hH g hg
  have hsq : ((Over.pullback V.ι).map F).left ≫ pullback.fst H.hom V.ι = pullback.fst G.hom V.ι ≫ F.left := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have hex : f.left ≫ ψ = φ ≫ F.left := by
    rw [← hw₂, ← hFg, hsq, ← Category.assoc, hw₁]
  refine ⟨F, ⟨hF, hex⟩, ?_⟩
  rintro F₂ ⟨-, hF₂⟩
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  have hpb : IsPullback G'.hom φ j G.hom := hφ.1.flip
  have _ : IsSchemeTheoreticallyDominant φ := IsSchemeTheoreticallyDominant.of_isPullback hpb
  apply Over.OverMorphism.ext
  exact IsGenericPointHom.hom_ext_lemma H.hom (by rw [Over.w, Over.w]) φ (hF₂.symm.trans hex)

private theorem pullback_map_eq_iff_fst_comp {S₀ U₀ : Scheme.{0}} {t : U₀ ⟶ S₀} {G₀ H₀ : Over S₀} (F : G₀ ⟶ H₀)
    (f : (Over.pullback t).obj G₀ ⟶ (Over.pullback t).obj H₀) :
    (Over.pullback t).map F = f ↔ f.left ≫ pullback.fst H₀.hom t = pullback.fst G₀.hom t ≫ F.left := by
  constructor
  · rintro rfl
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  · intro hF
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, pullback.lift_fst]
      exact hF.symm
    · simp only [Over.pullback_map_left, pullback.lift_snd]
      exact (Over.w f).symm

theorem of_isGenericPointHom (h : SemiAbelianHomExtension) (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (hj : IsGenericPointHom j) {G H : Over S} [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H) [IsMonHom f] :
    ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback j).map F = f := by
  obtain ⟨F, ⟨hF, hFf⟩, u⟩ := generic_of_isGrpPullback h hS hj hG hH
    (IsGenericPointHom.isGrpPullback_pullback_fst j G) (IsGenericPointHom.isGrpPullback_pullback_fst j H) f
  exact ⟨F, ⟨hF, (pullback_map_eq_iff_fst_comp F f).2 hFf⟩, fun F' ⟨hF', e⟩ => u F' ⟨hF', (pullback_map_eq_iff_fst_comp F' f).1 e⟩⟩

theorem generic_existsUnique_iso_of_isGrpPullback (h : SemiAbelianHomExtension)
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (hj : IsGenericPointHom j)
    {G H : Over S} [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) {G' H' : Over U}
    [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G j φ)
    (hψ : IsGrpPullback H' H j ψ) (e : G' ≅ H') [IsMonHom e.hom] :
    ∃! E : G ≅ H, IsMonHom E.hom ∧ e.hom.left ≫ ψ = φ ≫ E.hom.left := by
  obtain ⟨E₁, ⟨h₁, c₁⟩, u₁⟩ := generic_of_isGrpPullback h hS hj hG hH hφ hψ e.hom
  obtain ⟨E₂, ⟨h₂, c₂⟩, -⟩ := generic_of_isGrpPullback h hS hj hH hG hψ hφ e.inv
  obtain ⟨FG, -, uG⟩ := generic_of_isGrpPullback h hS hj hG hG hφ hφ (𝟙 G')
  obtain ⟨FH, -, uH⟩ := generic_of_isGrpPullback h hS hj hH hH hψ hψ (𝟙 H')
  have k₁ : E₁ ≫ E₂ = 𝟙 G := by
    rw [uG (E₁ ≫ E₂) ⟨inferInstance, by rw [Over.comp_left, ← Category.assoc, ← c₁, Category.assoc, ← c₂,
      ← Category.assoc, ← Over.comp_left, e.hom_inv_id]⟩, uG (𝟙 G) ⟨inferInstance, by simp⟩]
  have k₂ : E₂ ≫ E₁ = 𝟙 H := by
    rw [uH (E₂ ≫ E₁) ⟨inferInstance, by rw [Over.comp_left, ← Category.assoc, ← c₂, Category.assoc, ← c₁,
      ← Category.assoc, ← Over.comp_left, e.inv_hom_id]⟩, uH (𝟙 H) ⟨inferInstance, by simp⟩]
  refine ⟨⟨E₁, E₂, k₁, k₂⟩, ⟨h₁, c₁⟩, ?_⟩
  rintro E ⟨hE, cE⟩
  exact Iso.ext (u₁ E.hom ⟨hE, cE⟩)

theorem generic_existsUnique_iso (h : SemiAbelianHomExtension) (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (hj : IsGenericPointHom j) {G H : Over S} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) (e : (Over.pullback j).obj G ≅ (Over.pullback j).obj H)
    [IsMonHom e.hom] : ∃! E : G ≅ H, IsMonHom E.hom ∧ (Over.pullback j).map E.hom = e.hom := by
  obtain ⟨E, ⟨hE, cE⟩, u⟩ := generic_existsUnique_iso_of_isGrpPullback h hS hj hG hH
    (IsGenericPointHom.isGrpPullback_pullback_fst j G) (IsGenericPointHom.isGrpPullback_pullback_fst j H) e
  exact ⟨E, ⟨hE, (pullback_map_eq_iff_fst_comp E.hom e.hom).2 cE⟩,
    fun E' ⟨hE', c⟩ => u E' ⟨hE', (pullback_map_eq_iff_fst_comp E'.hom e.hom).1 c⟩⟩

theorem generic_existsUnique_iso_of_extensions (h : SemiAbelianHomExtension)
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (hj : IsGenericPointHom j)
    {A : Over U} [GrpObj A] {G H : Over S} [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    {φ : A.left ⟶ G.left} {ψ : A.left ⟶ H.left} (hφ : IsGrpPullback A G j φ) (hψ : IsGrpPullback A H j ψ) :
    ∃! E : G ≅ H, IsMonHom E.hom ∧ φ ≫ E.hom.left = ψ := by
  have _ : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  obtain ⟨E, ⟨hE, cE⟩, uE⟩ :=
    generic_existsUnique_iso_of_isGrpPullback h hS hj hG hH hφ hψ (Iso.refl A)
  simp only [Iso.refl_hom, Over.id_left, Category.id_comp] at cE uE
  exact ⟨E, ⟨hE, cE.symm⟩, fun E' ⟨hE', cE'⟩ => uE E' ⟨hE', cE'.symm⟩⟩

theorem isNormalScheme_spec (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Sp
  intro x
  have _ : x.asIdeal.IsPrime := x.isPrime
  let _ : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
  have _ : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  have hle : x.asIdeal.primeCompl ≤ nonZeroDivisors R := fun r hr =>
    mem_nonZeroDivisors_of_ne_zero fun h0 => hr (h0 ▸ x.asIdeal.zero_mem)
  have _ : IsDomain ((Spec (CommRingCat.of R)).presheaf.stalk x) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  exact ⟨inferInstance, isIntegrallyClosed_of_isLocalization _ _ hle⟩

theorem fractionField_of_isGrpPullback (h : SemiAbelianHomExtension) {R K : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] {G H : Over (Sp R)}
    [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) {G' H' : Over (Sp K)} [GrpObj G']
    [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hφ : IsGrpPullback G' G (spMap (algebraMap R K)) φ) (hψ : IsGrpPullback H' H (spMap (algebraMap R K)) ψ)
    (f : G' ⟶ H') [IsMonHom f] : ∃! F : G ⟶ H, IsMonHom F ∧ f.left ≫ ψ = φ ≫ F.left :=
  generic_of_isGrpPullback h (isNormalScheme_spec R) (IsGenericPointHom.fractionField R K) hG hH hφ hψ f

end GlobalTheory.Published.SemiAbelianHomExtension

theorem GlobalTheory.Published.SemiAbelianHomExtension.generic (h : GlobalTheory.Published.SemiAbelianHomExtension) (S : Scheme.{0}) [IsIntegral S] [AlgebraicGeometry.IsNoetherian S]
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (G H : Over S) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (f : (Over.pullback (S.fromSpecStalk (genericPoint S))).obj G ⟶ (Over.pullback (S.fromSpecStalk (genericPoint S))).obj H) [IsMonHom f] :
    ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (S.fromSpecStalk (genericPoint S))).map F = f :=
  of_isGenericPointHom h hS (GlobalTheory.IsGenericPointHom.fromSpecStalk S) hG hH f

theorem GlobalTheory.Published.SemiAbelianHomExtension.fractionField (h : GlobalTheory.Published.SemiAbelianHomExtension) (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (G H : Over (Sp R)) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (f : (Over.pullback (spMap (algebraMap R K))).obj G ⟶ (Over.pullback (spMap (algebraMap R K))).obj H) [IsMonHom f] :
    ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (spMap (algebraMap R K))).map F = f :=
  of_isGenericPointHom h (isNormalScheme_spec R) (GlobalTheory.IsGenericPointHom.fractionField R K) hG hH f
