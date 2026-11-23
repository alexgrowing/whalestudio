import Mathlib

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory

namespace FlatDescent

universe u

variable {X Y Z : Scheme.{u}}

theorem injective_appTop_of_epi (p : Y ⟶ X) [Epi p] : Function.Injective p.appTop := by
  have : Epi (Scheme.Γ.rightOp.map p) :=
    have := ΓSpec.adjunction.isLeftAdjoint
    inferInstance
  have : Mono p.appTop := inferInstanceAs (Mono (Scheme.Γ.rightOp.map p).unop)
  exact ConcreteCategory.injective_of_mono_of_preservesPullback p.appTop

theorem exists_appTop_eq_of_effectiveEpi (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)) (hs : f.appTop s = g.appTop s) :
    ∃ a : Γ(X, ⊤), p.appTop a = s := by
  let E := RingHom.eqLocus f.appTop.hom g.appTop.hom
  let ι : CommRingCat.of E ⟶ Γ(Y, ⊤) := CommRingCat.ofHom E.subtype
  have hι : ι ≫ f.appTop = ι ≫ g.appTop := by
    ext x
    exact x.2
  have : HasPullback p p := inferInstance
  obtain ⟨u, hu⟩ := IsRegularEpi.exists_of_isKernelPair p h (Y.toSpecΓ ≫ Spec.map ι) (by
    rw [Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp,
      ← Spec.map_comp, hι])
  refine ⟨u.appTop ((Scheme.ΓSpecIso (.of E)).inv ⟨s, hs⟩), ?_⟩
  have h1 : (Scheme.ΓSpecIso (.of E)).inv ≫ u.appTop ≫ p.appTop = ι := by
    rw [← Scheme.Hom.comp_appTop, hu, Scheme.Hom.comp_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp
  exact congr($h1 ⟨s, hs⟩)

theorem appTop_appTop_eq {p : Y ⟶ X} {f g : Z ⟶ Y} (h : f ≫ p = g ≫ p) (a : Γ(X, ⊤)) :
    f.appTop (p.appTop a) = g.appTop (p.appTop a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, h]

theorem existsUnique_appTop_eq_iff (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)) :
    (∃! a : Γ(X, ⊤), p.appTop a = s) ↔ f.appTop s = g.appTop s := by
  refine ⟨?_, fun hs => ?_⟩
  · rintro ⟨a, rfl, -⟩
    exact appTop_appTop_eq h.w a
  · obtain ⟨a, ha⟩ := exists_appTop_eq_of_effectiveEpi p h s hs
    exact ⟨a, ha, fun b hb => injective_appTop_of_epi p (hb.trans ha.symm)⟩

theorem isUnit_appTop_iff (p : Y ⟶ X) [EffectiveEpi p] (a : Γ(X, ⊤)) :
    IsUnit (p.appTop a) ↔ IsUnit a := by
  refine ⟨fun ha => ?_, fun ha => ha.map p.appTop.hom⟩
  obtain ⟨t, ht⟩ := ha.exists_right_inv
  have h := IsPullback.of_hasPullback p p
  obtain ⟨b, rfl⟩ := exists_appTop_eq_of_effectiveEpi p h t (by
    have h1 := congrArg (pullback.fst p p).appTop.hom ht
    have h2 := congrArg (pullback.snd p p).appTop.hom ht
    rw [map_mul, map_one] at h1 h2
    rw [appTop_appTop_eq h.w a] at h1
    exact left_inv_eq_right_inv ((mul_comm _ _).trans h1) h2)
  exact IsUnit.of_mul_eq_one b (injective_appTop_of_epi p (by rw [map_mul, ht, map_one]))

theorem existsUnique_units_appTop_eq_iff (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)ˣ) :
    (∃! a : Γ(X, ⊤)ˣ, Units.map p.appTop.hom.toMonoidHom a = s) ↔
      Units.map f.appTop.hom.toMonoidHom s = Units.map g.appTop.hom.toMonoidHom s := by
  refine ⟨?_, fun hs => ?_⟩
  · rintro ⟨a, rfl, -⟩
    exact Units.ext (appTop_appTop_eq h.w a)
  · obtain ⟨a, ha⟩ := exists_appTop_eq_of_effectiveEpi p h s (congrArg Units.val hs)
    obtain ⟨a, rfl⟩ := (isUnit_appTop_iff p a).1 (ha ▸ s.isUnit)
    exact ⟨a, Units.ext ha, fun b hb => Units.ext <|
      injective_appTop_of_epi p ((congrArg Units.val hb).trans ha.symm)⟩

section Opens

theorem isPullback_resLE {p : Y ⟶ X} {f g : Z ⟶ Y} (h : IsPullback f g p p) (U : X.Opens)
    (W : Z.Opens) (hW : W = f ⁻¹ᵁ p ⁻¹ᵁ U) (hf : W ≤ f ⁻¹ᵁ p ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ p ⁻¹ᵁ U) :
    IsPullback (f.resLE _ W hf) (g.resLE _ W hg) (p ∣_ U) (p ∣_ U) := by
  subst hW
  have hc : ∀ s : PullbackCone (p ∣_ U) (p ∣_ U),
      (s.fst ≫ (p ⁻¹ᵁ U).ι) ≫ p = (s.snd ≫ (p ⁻¹ᵁ U).ι) ≫ p := fun s => by
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, s.condition_assoc]
  have hr : ∀ s : PullbackCone (p ∣_ U) (p ∣_ U),
      Set.range (h.lift _ _ (hc s)) ⊆ Set.range (f ⁻¹ᵁ p ⁻¹ᵁ U).ι := fun s => by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (h.lift _ _ _ x) ∈ p ⁻¹ᵁ U
    rw [← Scheme.Hom.comp_apply, h.lift_fst, Scheme.Hom.comp_apply]
    exact (s.fst x).2
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => IsOpenImmersion.lift (f ⁻¹ᵁ p ⁻¹ᵁ U).ι
    (h.lift _ _ (hc s)) (hr s)) (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_)⟩⟩
  · rw [← cancel_mono U.ι]
    simp [morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc, h.w]
  · rw [← cancel_mono (p ⁻¹ᵁ U).ι]
    simp
  · rw [← cancel_mono (p ⁻¹ᵁ U).ι]
    simp
  · rw [← cancel_mono (f ⁻¹ᵁ p ⁻¹ᵁ U).ι, IsOpenImmersion.lift_fac]
    refine h.hom_ext ?_ ?_
    · simp [← h₁]
    · simp [← h₂]

theorem appTop_resLE_apply (f : Z ⟶ Y) (V : Y.Opens) (W : Z.Opens) (e : W ≤ f ⁻¹ᵁ V)
    (s : Γ(Y, V)) : (f.resLE V W e).appTop (V.topIso.inv s) = W.topIso.inv (f.appLE V W e s) := by
  have : V.topIso.inv ≫ (f.resLE V W e).appTop = f.appLE V W e ≫ W.topIso.inv := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Iso.inv_hom_id_assoc]
  exact congr($this s)

theorem appTop_morphismRestrict_apply (p : Y ⟶ X) (U : X.Opens) (a : Γ(X, U)) :
    (p ∣_ U).appTop (U.topIso.inv a) = (p ⁻¹ᵁ U).topIso.inv (p.app U a) := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, appTop_resLE_apply, Scheme.Hom.appLE_eq_app]

theorem effectiveEpi_morphismRestrict (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    (U : X.Opens) : EffectiveEpi (p ∣_ U) := by
  have : Flat (p ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p U).flip ‹_›
  have : Surjective (p ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p U).flip ‹_›
  have : QuasiCompact (p ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p U).flip ‹_›
  infer_instance

theorem existsUnique_app_eq_iff (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    {f g : Z ⟶ Y} (h : IsPullback f g p p) (U : X.Opens) (W : Z.Opens) (hW : W = f ⁻¹ᵁ p ⁻¹ᵁ U)
    (hf : W ≤ f ⁻¹ᵁ p ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ p ⁻¹ᵁ U) (s : Γ(Y, p ⁻¹ᵁ U)) :
    (∃! a : Γ(X, U), p.app U a = s) ↔ f.appLE _ W hf s = g.appLE _ W hg s := by
  have := effectiveEpi_morphismRestrict p U
  have hb : ∀ {T : Scheme.{u}} (V : T.Opens), Function.Bijective V.topIso.inv := fun V =>
    ConcreteCategory.bijective_of_isIso _
  rw [← (hb W).1.eq_iff, ← appTop_resLE_apply, ← appTop_resLE_apply,
    ← existsUnique_appTop_eq_iff (p ∣_ U) (isPullback_resLE h U W hW hf hg),
    ← (Equiv.ofBijective _ (hb U)).existsUnique_congr_right]
  simp only [Equiv.ofBijective_apply, appTop_morphismRestrict_apply, (hb _).1.eq_iff]

theorem isUnit_app_iff (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p] (U : X.Opens)
    (a : Γ(X, U)) : IsUnit (p.app U a) ↔ IsUnit a := by
  have := effectiveEpi_morphismRestrict p U
  rw [← isUnit_map_iff (p ⁻¹ᵁ U).topIso.inv.hom, ← appTop_morphismRestrict_apply,
    isUnit_appTop_iff, isUnit_map_iff]

end Opens

end FlatDescent

end GlobalTheory
