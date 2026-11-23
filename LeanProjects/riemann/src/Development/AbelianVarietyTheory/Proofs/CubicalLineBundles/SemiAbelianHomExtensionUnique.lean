import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.DedekindExt

variable {X X' Y S : Scheme.{0}}

def Agree (φ : X' ⟶ X) (f : X' ⟶ Y) {W : Scheme.{0}} (i : W ⟶ X) (g : W ⟶ Y) : Prop :=
  ∀ (T : Scheme.{0}) (u : T ⟶ W) (u' : T ⟶ X'), u ≫ i = u' ≫ φ → u ≫ g = u' ≫ f

theorem Agree.comp {φ : X' ⟶ X} {f : X' ⟶ Y} {W W' : Scheme.{0}} {i : W ⟶ X} {g : W ⟶ Y}
    (h : Agree φ f i g) (c : W' ⟶ W) : Agree φ f (c ≫ i) (c ≫ g) := fun T u u' e => by
  rw [← Category.assoc]
  exact h T _ _ (by rw [Category.assoc, e])

theorem Agree.of_dominant {φ : X' ⟶ X} [Flat φ] {f : X' ⟶ Y} (sX : X ⟶ S) (sY : Y ⟶ S) [IsSeparated sY]
    (hf : f ≫ sY = φ ≫ sX) {W W' : Scheme.{0}} {i : W ⟶ X} {g : W ⟶ Y} (hg : g ≫ sY = i ≫ sX)
    (c : W' ⟶ W) [QuasiCompact c] [IsSchemeTheoreticallyDominant c] (h : Agree φ f (c ≫ i) (c ≫ g)) :
    Agree φ f i g := by
  have key : pullback.fst i φ ≫ g = pullback.snd i φ ≫ f := by
    have : IsSchemeTheoreticallyDominant (pullback.snd c (pullback.fst i φ)) :=
      .of_isPullback (IsPullback.of_hasPullback c (pullback.fst i φ))
    refine ExtUnique.hom_ext_of_dominant sY ?_ (pullback.snd c (pullback.fst i φ)) ?_
    · rw [Category.assoc, Category.assoc, hg, hf, pullback.condition_assoc]
    · rw [← pullback.condition_assoc, ← Category.assoc (pullback.snd _ _)]
      refine h _ _ _ ?_
      rw [pullback.condition_assoc, Category.assoc, pullback.condition]
  intro T u u' e
  rw [← pullback.lift_fst u u' e, Category.assoc, key, pullback.lift_snd_assoc]

theorem exists_open_agree [IsLocallyNoetherian X] {φ : X' ⟶ X} [Flat φ] {f : X' ⟶ Y} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsSeparated sY] [LocallyOfFiniteType sY] (hf : f ≫ sY = φ ≫ sX) (x : X)
    (g : Spec (X.presheaf.stalk x) ⟶ Y) (hg : g ≫ sY = X.fromSpecStalk x ≫ sX)
    (h : Agree φ f (X.fromSpecStalk x) g) :
    ∃ (W : Scheme.{0}) (i : W ⟶ X) (_ : IsOpenImmersion i) (g' : W ⟶ Y),
      x ∈ Set.range i ∧ g' ≫ sY = i ≫ sX ∧ Agree φ f i g' := by
  obtain ⟨U, hxU, g₁, h₁, h₂⟩ := spread_out_of_isGermInjective' sX sY g hg
  obtain ⟨V, hxV, hV, hVU, hinj⟩ := X.exists_le_and_germ_injective x U hxU
  have hr : Set.range hV.fromSpec ⊆ Set.range U.ι := by
    rw [hV.range_fromSpec, Scheme.Opens.range_ι]; exact hVU
  let l := IsOpenImmersion.lift U.ι hV.fromSpec hr
  have hl : l ≫ U.ι = hV.fromSpec := IsOpenImmersion.lift_fac _ _ _
  have hc : Spec.map (X.presheaf.germ V x hxV) ≫ hV.fromSpec = X.fromSpecStalk x :=
    hV.fromSpecStalk_eq_fromSpecStalk hxV
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hinj
  have hg' : (l ≫ g₁) ≫ sY = hV.fromSpec ≫ sX := by rw [Category.assoc, h₂, ← Category.assoc, hl]
  refine ⟨_, hV.fromSpec, inferInstance, l ≫ g₁, by rw [hV.range_fromSpec]; exact hxV, hg',
    Agree.of_dominant sX sY hf hg' (Spec.map (X.presheaf.germ V x hxV)) ?_⟩
  have e : Spec.map (X.presheaf.germ V x hxV) ≫ l = U.fromSpecStalkOfMem x hxU := by
    rw [← cancel_mono U.ι, Category.assoc, hl, hc, Scheme.Opens.fromSpecStalkOfMem_ι]
  rw [hc, ← Category.assoc, e, ← h₁]
  exact h

theorem exists_of_locally {U : Scheme.{0}} {j : U ⟶ S} [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    {φ : X' ⟶ X} {p : X' ⟶ U} {f : X' ⟶ Y} (sX : X ⟶ S) [Flat sX] (sY : Y ⟶ S) [IsSeparated sY]
    (hp : IsPullback φ p sX j)
    (h : ∀ x : X, ∃ (W : Scheme.{0}) (i : W ⟶ X) (_ : IsOpenImmersion i) (g' : W ⟶ Y),
      x ∈ Set.range i ∧ g' ≫ sY = i ≫ sX ∧ Agree φ f i g') :
    ∃ F : X ⟶ Y, F ≫ sY = sX ∧ φ ≫ F = f := by
  choose W i hι g hx hg ha using h
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers X W i (fun x => ⟨x, hx x⟩)
  have : QuasiCompact φ := MorphismProperty.of_isPullback hp.flip ‹_›
  have : IsSchemeTheoreticallyDominant φ := .of_isPullback hp.flip
  have hc : ∀ x y, pullback.fst (i x) (i y) ≫ g x = pullback.snd (i x) (i y) ≫ g y := by
    intro x y
    let q := pullback.fst (i x) (i y) ≫ i x
    have : IsSchemeTheoreticallyDominant (pullback.fst q φ) :=
      .of_isPullback (IsPullback.of_hasPullback q φ).flip
    refine ExtUnique.hom_ext_of_dominant sY ?_ (pullback.fst q φ) ?_
    · rw [Category.assoc, Category.assoc, hg, hg, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc]
      refine (ha x _ _ (pullback.snd q φ) ?_).trans (ha y _ _ (pullback.snd q φ) ?_).symm
      · rw [Category.assoc]; exact pullback.condition
      · rw [Category.assoc, ← pullback.condition]; exact pullback.condition
  have hF : ∀ x, i x ≫ 𝒰.glueMorphisms g hc = g x := fun x => 𝒰.ι_glueMorphisms g hc x
  refine ⟨𝒰.glueMorphisms g hc, 𝒰.hom_ext _ _ fun x : X => ?_,
    Scheme.Cover.hom_ext (𝒰.pullback₁ φ) _ _ fun x : X => ?_⟩
  · change i x ≫ _ = i x ≫ _
    rw [← Category.assoc, hF, hg]
  · change pullback.fst φ (i x) ≫ _ = pullback.fst φ (i x) ≫ _
    rw [pullback.condition_assoc, hF]
    exact ha x _ _ _ pullback.condition.symm

theorem exists_of_stalks [IsLocallyNoetherian X] {U : Scheme.{0}} {j : U ⟶ S} [QuasiCompact j] [Flat j]
    [IsSchemeTheoreticallyDominant j]
    {φ : X' ⟶ X} {p : X' ⟶ U} {f : X' ⟶ Y} (sX : X ⟶ S) [Flat sX] (sY : Y ⟶ S) [IsSeparated sY]
    [LocallyOfFiniteType sY] (hp : IsPullback φ p sX j) (hf : f ≫ sY = φ ≫ sX)
    (h : ∀ s : S, ∃ (T : Scheme.{0}) (t : T ⟶ S) (a : Spec (S.presheaf.stalk s) ⟶ T) (g : pullback sX t ⟶ Y),
      a ≫ t = S.fromSpecStalk s ∧ g ≫ sY = pullback.fst sX t ≫ sX ∧ Agree φ f (pullback.fst sX t) g) :
    ∃ F : X ⟶ Y, F ≫ sY = sX ∧ φ ≫ F = f := by
  have : Flat φ := MorphismProperty.of_isPullback hp.flip ‹_›
  refine exists_of_locally sX sY hp fun x => ?_
  obtain ⟨T, t, a, g, ha, hg, hA⟩ := h (sX x)
  have e : X.fromSpecStalk x ≫ sX = (Spec.map (sX.stalkMap x) ≫ a) ≫ t := by
    rw [Category.assoc, ha, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have h₁ := hA.comp (pullback.lift _ _ e)
  rw [pullback.lift_fst] at h₁
  exact exists_open_agree sX sY hf x _ (by rw [Category.assoc, hg, pullback.lift_fst_assoc]) h₁

theorem exists_spec_factor (R T : Type) [CommRing R] [CommRing T] [Algebra R T] (M : Submonoid R)
    [IsLocalization M T] {A : CommRingCat.{0}} (ψ : CommRingCat.of R ⟶ A) (hu : ∀ y : M, IsUnit (ψ.hom y)) :
    ∃ a : Spec A ⟶ Sp T, a ≫ spMap (algebraMap R T) = Spec.map ψ := by
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.lift (S := T) hu)), ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact IsLocalization.lift_eq hu r

theorem exists_fromSpecStalk_factor (R T : Type) [CommRing R] [CommRing T] [Algebra R T] (M : Submonoid R)
    [IsLocalization M T] (s : PrimeSpectrum R) (hM : M ≤ s.asIdeal.primeCompl) :
    ∃ a : Spec ((Sp R).presheaf.stalk s) ⟶ Sp T, a ≫ spMap (algebraMap R T) = (Sp R).fromSpecStalk s := by
  have hu : ∀ y : M, IsUnit ((StructureSheaf.toStalk R s).hom y) := fun y =>
    IsLocalization.map_units ((Spec.structureSheaf R).presheaf.stalk s) (⟨y.1, hM y.2⟩ : s.asIdeal.primeCompl)
  obtain ⟨a, ha⟩ := exists_spec_factor R T M (StructureSheaf.toStalk R s) hu
  exact ⟨a, ha.trans (Spec.fromSpecStalk_eq' (CommRingCat.of R) s).symm⟩

theorem exists_agree_of_extend {U T : Scheme.{0}} {k : U ⟶ T} {t : T ⟶ S} [Mono t] {j : U ⟶ S} (hj : k ≫ t = j)
    (G G' : Over S) [GrpObj G] [GrpObj G'] (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') [IsMonHom f]
    (h : ∀ f' : (Over.pullback k).obj ((Over.pullback t).obj G) ⟶ (Over.pullback k).obj ((Over.pullback t).obj G'),
      IsMonHom f' → ∃ F, (Over.pullback k).map F = f') :
    ∃ g : pullback G.hom t ⟶ G'.left, g ≫ G'.hom = pullback.fst G.hom t ≫ G.hom ∧
      Agree (pullback.fst G.hom j) (f.left ≫ pullback.fst G'.hom j) (pullback.fst G.hom t) g := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G j)
    (((isGrpPullback_pullback _ k).comp (isGrpPullback_pullback G t)).congr hj rfl)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback G' j)
    (((isGrpPullback_pullback _ k).comp (isGrpPullback_pullback G' t)).congr hj rfl)
  obtain ⟨F, hF⟩ := h (a.inv ≫ f ≫ b.hom) inferInstance
  have hF' : (a.hom ≫ (Over.pullback k).map F).left = (f ≫ b.hom).left := by rw [hF, a.hom_inv_id_assoc]
  have hw : F.left ≫ pullback.snd G'.hom t = pullback.snd G.hom t := Over.w F
  have hw' : a.hom.left ≫ pullback.snd ((Over.pullback t).obj G).hom k = pullback.snd G.hom j := Over.w a.hom
  refine ⟨F.left ≫ pullback.fst G'.hom t, ?_, fun Z u u' e => ?_⟩
  · refine (Category.assoc _ _ _).trans ?_
    rw [pullback.condition, pullback.condition, ← hw]
    exact (Category.assoc _ _ _).symm
  · have key : (a.hom.left ≫ pullback.fst ((Over.pullback t).obj G).hom k) ≫ F.left ≫ pullback.fst G'.hom t =
        f.left ≫ pullback.fst G'.hom j := by
      have h₁ := ExtUnique.pullback_map_left_fst k F
      rw [Over.comp_left, Over.comp_left] at hF'
      rw [← hb', ← reassoc_of% hF', reassoc_of% h₁]
      exact Category.assoc _ _ _
    have hfst : (a.hom.left ≫ pullback.fst ((Over.pullback t).obj G).hom k) ≫ pullback.fst G.hom t =
        pullback.fst G.hom j := (Category.assoc _ _ _).trans ha'
    have hu : u = u' ≫ (a.hom.left ≫ pullback.fst ((Over.pullback t).obj G).hom k) := by
      have : Mono (pullback.fst G.hom t) := inferInstance
      rw [← cancel_mono (pullback.fst G.hom t), e]
      exact (congrArg (u' ≫ ·) hfst.symm).trans (Category.assoc _ _ _).symm
    rw [hu]
    exact (Category.assoc _ _ _).trans (congrArg (u' ≫ ·) key)

end GlobalTheory.DedekindExt

namespace GlobalTheory

open DedekindExt

theorem abelianScheme_hom_extends_dedekind :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G G' : Over (Sp R)) [GrpObj G] [GrpObj G'], IsAbelianScheme G → IsAbelianScheme G' → ∀ f : (Over.pullback (spMap (algebraMap R K))).obj G ⟶ (Over.pullback (spMap (algebraMap R K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap R K))).map F = f := by
  intro H R K _ _ _ _ _ G G' _ _ hG hG' f hf
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R K
  have := hG.smooth
  have := hG'.proper
  have : IsPreimmersion (spMap (algebraMap R K)) := .of_isLocalization (nonZeroDivisors R)
  have : Flat (spMap (algebraMap R K)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors R))
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have hw : f.left ≫ pullback.snd G'.hom _ = pullback.snd G.hom _ := Over.w f
  have hf₀ : (f.left ≫ pullback.fst G'.hom _) ≫ G'.hom = pullback.fst G.hom _ ≫ G.hom := by
    refine (Category.assoc _ _ _).trans ?_
    rw [pullback.condition, pullback.condition, ← hw]
    exact (Category.assoc _ _ _).symm
  obtain ⟨F, hF, hF'⟩ := exists_of_stalks G.hom G'.hom (IsPullback.of_hasPullback G.hom (spMap (algebraMap R K)))
    hf₀ fun s : PrimeSpectrum R => by
      by_cases hs : s.asIdeal = ⊥
      · obtain ⟨a, ha⟩ := exists_fromSpecStalk_factor R K (nonZeroDivisors R) s fun r hr hr' =>
          nonZeroDivisors.ne_zero hr (by simpa [hs] using hr')
        refine ⟨_, _, a, _, ha, hf₀, fun Z u u' e => ?_⟩
        rw [(cancel_mono _).1 e]
      · let T := Localization.AtPrime s.asIdeal
        have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hs T
        letI : Algebra T K := IsLocalization.localizationAlgebraOfSubmonoidLe T K s.asIdeal.primeCompl
          (nonZeroDivisors R) s.asIdeal.primeCompl_le_nonZeroDivisors
        have : IsScalarTower R T K := IsLocalization.localization_isScalarTower_of_submonoid_le T K _ _ _
        have : IsFractionRing T K :=
          IsFractionRing.isFractionRing_of_isDomain_of_isLocalization s.asIdeal.primeCompl T K
        have : IsPreimmersion (spMap (algebraMap R T)) := .of_isLocalization s.asIdeal.primeCompl
        obtain ⟨a, ha⟩ := exists_fromSpecStalk_factor R T s.asIdeal.primeCompl s le_rfl
        have hj : spMap (algebraMap T K) ≫ spMap (algebraMap R T) = spMap (algebraMap R K) := by
          rw [← Spec.map_comp, IsScalarTower.algebraMap_eq R T K]; rfl
        obtain ⟨g, hg, hA⟩ := exists_agree_of_extend hj G G' f fun f' hf' => by
          obtain ⟨F, hF, -⟩ := H T K _ _
            (isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_pullback_obj _ G hG))
            (isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_pullback_obj _ G' hG')) f' hf'
          exact ⟨F, hF.2⟩
        exact ⟨_, _, a, g, ha, hg, hA⟩
  have e : (Over.pullback (spMap (algebraMap R K))).map (Over.homMk F hF : G ⟶ G') = f := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (ExtUnique.pullback_map_left_fst _ _).trans hF'
    · exact (Over.w _).trans (Over.w _).symm
  refine ⟨Over.homMk F hF, ⟨ExtUnique.isMonHom_of_pullback _ _ (e ▸ hf), e⟩, fun F' hF'' => ?_⟩
  exact ExtUnique.pullback_map_injective _ G G' (hF''.2.trans e.symm)

end GlobalTheory
