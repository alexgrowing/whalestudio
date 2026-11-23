import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDescentSectionsInjectiveEqualizerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MorDescent

theorem restrict_isPullback {R : Type} [CommRing R] {S Y Z Y' : Scheme.{0}} {π : S ⟶ Sp R} {y : Y ⟶ Sp R}
    {p : Z ⟶ Y} {q : Z ⟶ S} (hpb : IsPullback p q y π) (f : Y' ⟶ Y) :
    IsPullback (pullback.snd p f) (pullback.fst p f ≫ q) (f ≫ y) π :=
  IsPullback.paste_vert (IsPullback.of_hasPullback p f).flip hpb

theorem uniq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ (W : Scheme.{0}) (g₁ g₂ : Y ⟶ W), p ≫ g₁ = p ≫ g₂ → g₁ = g₂ := by
  intro R _ _ _ _ S Y Z π y p q hprop hsurj hint hflat hpb W g₁ g₂ he
  have hpS : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hsurj
  have heqz := GlobalTheory.T.flat_descent_sections_injective_equalizer R S Y Z π y p q hprop hsurj hint hflat hpb
  have hbase : g₁.base = g₂.base := by
    ext x
    obtain ⟨z, rfl⟩ := p.surjective x
    have := congrArg (fun k : Z ⟶ W => k z) he
    simpa only [Scheme.Hom.comp_apply] using this
  refine Scheme.Hom.ext hbase fun U => ?_
  have : Mono (p.app (g₂ ⁻¹ᵁ U)) := ConcreteCategory.mono_of_injective _ (heqz _).1
  rw [← cancel_mono (p.app (g₂ ⁻¹ᵁ U)), ← Scheme.Hom.comp_app, Scheme.Hom.congr_app he.symm,
    Category.assoc, Scheme.Hom.naturality, ← Category.assoc, ← Scheme.Hom.comp_app]
  rfl

theorem exAff : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ (W : Scheme.{0}) [IsAffine W] (h : Z ⟶ W), pullback.fst p p ≫ h = pullback.snd p p ≫ h → ∃ h₀ : Y ⟶ W, p ≫ h₀ = h := by
  intro R _ _ _ _ S Y Z π y p q hprop hsurj hint hflat hpb W _ h hh
  obtain ⟨hinj, hdesc⟩ := GlobalTheory.T.flat_descent_sections_injective_equalizer R S Y Z π y p q hprop hsurj hint hflat hpb ⊤
  have hmem : ∀ x : Γ(W, ⊤), h.appTop x ∈ (p.app ⊤).hom.range := by
    intro x
    refine hdesc (h.appTop x) fun e => ?_
    have := congrArg (fun k : pullback p p ⟶ W => k.appTop.hom x) hh
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
    refine this.trans ?_
    change _ = (CommRingCat.Hom.hom ((pullback p p).presheaf.map (𝟙 (Opposite.op (⊤ : (pullback p p).Opens)))))
      ((pullback.snd p p).appTop.hom (h.appTop.hom x))
    rw [CategoryTheory.Functor.map_id]
    rfl
  let φ : Γ(W, ⊤) →+* Γ(Y, ⊤) :=
    (RingEquiv.ofBijective (p.app ⊤).hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (p.app ⊤).hom.rangeRestrict_surjective⟩).symm.toRingHom.comp
      (h.appTop.hom.codRestrict _ hmem)
  have hφ : CommRingCat.ofHom φ ≫ p.appTop = h.appTop := by
    ext x
    exact congrArg Subtype.val ((RingEquiv.ofBijective (p.app ⊤).hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (p.app ⊤).hom.rangeRestrict_surjective⟩).apply_symm_apply
      (h.appTop.hom.codRestrict _ hmem x))
  refine ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ W.isoSpec.inv, ?_⟩
  have h1 : h = Z.toSpecΓ ≫ Spec.map h.appTop ≫ W.isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  rw [h1, ← Category.assoc p, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp_assoc, hφ]

theorem descend : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ h : Z ⟶ W, pullback.fst p p ≫ h = pullback.snd p p ≫ h → ∃! h₀ : Y ⟶ W, p ≫ h₀ = h := by
  intro R _ _ _ _ S Y Z W π y p q hprop hsurj hint hflat hpb h hh
  have hpS : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hsurj
  have hpC : UniversallyClosed p := MorphismProperty.of_isPullback (P := @UniversallyClosed) hpb.flip inferInstance
  have hfib : Function.FactorsThrough h.base.hom p.base.hom := by
    intro a b hab
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := p) a b hab
    have := congrArg (fun k : pullback p p ⟶ W => k z) hh
    simp only [Scheme.Hom.comp_apply, hz1, hz2] at this
    exact this
  have hq : Topology.IsQuotientMap p.base.hom :=
    IsClosedMap.isQuotientMap p.isClosedMap p.base.hom.continuous p.surjective
  let b : Y.carrier ⟶ W.carrier := TopCat.ofHom (hq.lift h.base.hom hfib)
  have hb : ∀ z, b (p z) = h z := fun z => congrArg (fun k : C(Z, W) => k z) (hq.lift_comp h.base.hom hfib)
  let V : W.affineOpens → Y.Opens := fun i => TopologicalSpace.Opens.comap b.hom i.1
  have hV : TopologicalSpace.IsOpenCover V := W.isBasis_affineOpens.isOpenCover.comap b.hom
  let 𝒰 := Y.openCoverOfIsOpenCover V hV
  have hloc : ∀ i, ∃ u : (V i).toScheme ⟶ W, pullback.snd p (V i).ι ≫ u = pullback.fst p (V i).ι ≫ h := by
    intro i
    have hr : Set.range (pullback.fst p (V i).ι ≫ h) ⊆ Set.range i.1.ι := by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, ← hb, ← Scheme.Hom.comp_apply, pullback.condition,
        Scheme.Hom.comp_apply]
      exact ((pullback.snd p (V i).ι) w).2
    let hi := IsOpenImmersion.lift i.1.ι _ hr
    have : IsAffine i.1.toScheme := i.2
    have heq : pullback.fst (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ≫ hi =
        pullback.snd (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ≫ hi := by
      rw [← cancel_mono i.1.ι]
      simp only [Category.assoc, hi, IsOpenImmersion.lift_fac]
      let m : pullback (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ⟶ pullback p p :=
        pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst _ _)
          (by simp only [Category.assoc, pullback.condition, pullback.condition_assoc])
      have e1 : pullback.fst (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ≫ pullback.fst p (V i).ι =
          m ≫ pullback.fst p p := (pullback.lift_fst _ _ _).symm
      have e2 : pullback.snd (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ≫ pullback.fst p (V i).ι =
          m ≫ pullback.snd p p := (pullback.lift_snd _ _ _).symm
      rw [reassoc_of% e1, reassoc_of% e2, hh]
    obtain ⟨u, hu⟩ := exAff R S (V i).toScheme (pullback p (V i).ι) π ((V i).ι ≫ y) (pullback.snd p (V i).ι)
      (pullback.fst p (V i).ι ≫ q) hprop hsurj hint inferInstance (restrict_isPullback hpb _) i.1.toScheme hi heq
    exact ⟨u ≫ i.1.ι, by rw [← Category.assoc, hu, IsOpenImmersion.lift_fac]⟩
  choose u hu using hloc
  have hc : ∀ i j, pullback.fst (V i).ι (V j).ι ≫ u i = pullback.snd (V i).ι (V j).ι ≫ u j := by
    intro i j
    let f := pullback.fst (V i).ι (V j).ι ≫ (V i).ι
    apply uniq R S _ (pullback p f) π (f ≫ y) (pullback.snd p f) (pullback.fst p f ≫ q) hprop hsurj hint
      inferInstance (restrict_isPullback hpb f) W
    let mi : pullback p f ⟶ pullback p (V i).ι := pullback.lift (pullback.fst p f)
      (pullback.snd p f ≫ pullback.fst _ _) (by rw [pullback.condition, Category.assoc])
    let mj : pullback p f ⟶ pullback p (V j).ι := pullback.lift (pullback.fst p f)
      (pullback.snd p f ≫ pullback.snd _ _) (by
        rw [pullback.condition]
        show pullback.snd p f ≫ pullback.fst (V i).ι (V j).ι ≫ (V i).ι = _
        rw [pullback.condition, Category.assoc])
    have ei : pullback.snd p f ≫ pullback.fst (V i).ι (V j).ι = mi ≫ pullback.snd p (V i).ι :=
      (pullback.lift_snd _ _ _).symm
    have ej : pullback.snd p f ≫ pullback.snd (V i).ι (V j).ι = mj ≫ pullback.snd p (V j).ι :=
      (pullback.lift_snd _ _ _).symm
    rw [reassoc_of% ei, reassoc_of% ej, hu, hu, pullback.lift_fst_assoc, pullback.lift_fst_assoc]
  have hglue : p ≫ 𝒰.glueMorphisms u hc = h := by
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ p) _ _ fun i => ?_
    change pullback.fst p (V i).ι ≫ _ = pullback.fst p (V i).ι ≫ _
    rw [← Category.assoc, pullback.condition, Category.assoc]
    change pullback.snd p (V i).ι ≫ 𝒰.f i ≫ _ = _
    exact (congrArg (pullback.snd p (V i).ι ≫ ·) (𝒰.ι_glueMorphisms u hc i)).trans (hu i)
  refine ⟨𝒰.glueMorphisms u hc, hglue, fun g hg => ?_⟩
  exact uniq R S Y Z π y p q hprop hsurj hint hflat hpb W g _ (hg.trans hglue.symm)

end GlobalTheory.MorDescent
