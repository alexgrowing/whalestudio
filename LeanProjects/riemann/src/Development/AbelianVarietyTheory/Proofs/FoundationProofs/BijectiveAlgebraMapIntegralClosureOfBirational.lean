import Mathlib

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology

namespace GlobalTheory

universe u

section Normal

variable {X Y : Scheme.{u}}

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

theorem _root_.GlobalTheory.isIntegrallyClosed_sections_of_stalks [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) {U : Y.Opens} (hU : IsAffineOpen U)
    [Nonempty U] : IsIntegrallyClosed Γ(Y, U) := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ _ => ?_
  let q : PrimeSpectrum Γ(Y, U) := ⟨p, inferInstance⟩
  have hq : hU.fromSpec q ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨q, rfl⟩
  letI := Y.presheaf.algebra_section_stalk (U := U) ⟨hU.fromSpec q, hq⟩
  haveI : IsLocalization p.primeCompl (Y.presheaf.stalk (hU.fromSpec q)) :=
    hU.isLocalization_stalk' q hq
  haveI := hY (hU.fromSpec q)
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (Y.presheaf.stalk (hU.fromSpec q))
      (Localization.AtPrime p)).toRingEquiv

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

theorem _root_.GlobalTheory.apply_genericPoint_of_isDominant (f : X ⟶ Y) [IsDominant f] [IrreducibleSpace X]
    [IrreducibleSpace Y] : f (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at h
  exact h.eq (genericPoint_spec Y)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

theorem _root_.GlobalTheory.isFractionRing_stalk_of_eq_genericPoint [IsIntegral Y] {U : Y.Opens} (hU : IsAffineOpen U)
    (y : Y) (hyU : y ∈ U) (hy : y = genericPoint Y) :
    letI := Y.presheaf.algebra_section_stalk (U := U) ⟨y, hyU⟩
    IsFractionRing Γ(Y, U) (Y.presheaf.stalk y) := by
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  subst hy
  exact functionField_isFractionRing_of_isAffineOpen Y U hU

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in
private lemma app_injective_and_exists_app_eq_of_isIntegral (f : X ⟶ Y) [IsIntegral X]
    [IsIntegral Y] [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) {U : Y.Opens} (hU : IsAffineOpen U)
    [Nonempty U] :
    Function.Injective (f.app U) ∧ ∀ s : Γ(X, f ⁻¹ᵁ U),
      (letI := (f.app U).hom.toAlgebra; IsIntegral Γ(Y, U) s) → ∃ r, f.app U r = s := by
  have h2 : f (genericPoint X) = genericPoint Y := _root_.GlobalTheory.apply_genericPoint_of_isDominant f
  obtain ⟨y, hy⟩ := ‹Nonempty U›
  have hηU : f (genericPoint X) ∈ U := by
    rw [h2]; exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).2 ⟨y, trivial, hy⟩
  letI := Y.presheaf.algebra_section_stalk (U := U) ⟨_, hηU⟩
  haveI := _root_.GlobalTheory.isFractionRing_stalk_of_eq_genericPoint hU _ hηU h2
  haveI := _root_.GlobalTheory.isIntegrallyClosed_sections_of_stalks hY hU
  have hsq := f.germ_stalkMap_apply U (genericPoint X) hηU
  have hgX := germ_injective_of_isIntegral X (U := f ⁻¹ᵁ U) (genericPoint X) hηU
  have hg := ConcreteCategory.bijective_of_isIso (f.stalkMap (genericPoint X))
  have hgY : Function.Injective (Y.presheaf.germ U _ hηU) :=
    IsFractionRing.injective Γ(Y, U) (Y.presheaf.stalk (f (genericPoint X)))
  refine ⟨fun a b hab => hgY (hg.1 ?_), fun s hs => ?_⟩
  · rw [hsq, hsq, hab]
  · letI := (f.app U).hom.toAlgebra
    let ψ := (inv (f.stalkMap (genericPoint X))).hom.comp (X.presheaf.germ (f ⁻¹ᵁ U) _ hηU).hom
    have hψ : (algebraMap Γ(Y, U) (Y.presheaf.stalk (f (genericPoint X)))).comp (RingHom.id _) =
        ψ.comp (algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
      ext a
      change Y.presheaf.germ U _ hηU a = (inv (f.stalkMap (genericPoint X))).hom
        (X.presheaf.germ (f ⁻¹ᵁ U) _ hηU (f.app U a))
      rw [← hsq, ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hs.map_of_comp_eq (RingHom.id _) ψ hψ)
    have hr' : Y.presheaf.germ U _ hηU r =
        (inv (f.stalkMap (genericPoint X))).hom (X.presheaf.germ (f ⁻¹ᵁ U) _ hηU s) := hr
    refine ⟨r, hgX ?_⟩
    rw [← hsq, hr', ← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in
private lemma bijective_algebraMap_integralClosure_of_isIntegrallyClosed (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    Function.Bijective (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))) := by
  letI := (f.app U).hom.toAlgebra
  rcases isEmpty_or_nonempty U with hE | hN
  · have hU0 : U = ⊥ := by
      ext x
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hE.false ⟨x, hx⟩
    subst hU0
    have h01 : (0 : integralClosure Γ(Y, ⊥) Γ(X, f ⁻¹ᵁ ⊥)) = 1 := by
      rw [← map_zero (algebraMap Γ(Y, ⊥) (integralClosure Γ(Y, ⊥) Γ(X, f ⁻¹ᵁ ⊥))),
        ← map_one (algebraMap Γ(Y, ⊥) (integralClosure Γ(Y, ⊥) Γ(X, f ⁻¹ᵁ ⊥))),
        Subsingleton.elim (0 : Γ(Y, ⊥)) 1]
    haveI := subsingleton_of_zero_eq_one h01
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  · obtain ⟨hinj, hex⟩ := app_injective_and_exists_app_eq_of_isIntegral f hY hU
    refine ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun b => ?_⟩
    obtain ⟨r, hr⟩ := hex b.1 b.2
    exact ⟨r, Subtype.ext hr⟩

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

theorem _root_.GlobalTheory.isIso_fromNormalization_of_birational (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsIso f.fromNormalization := by
  have hpiece : ∀ U : Y.affineOpens,
      IsIso (Spec.map ((f.normalizationDiagramMap).app (Opposite.op U.1))) := by
    intro U
    haveI : IsIso ((f.normalizationDiagramMap).app (Opposite.op U.1)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (bijective_algebraMap_integralClosure_of_isIntegrallyClosed f hY U.2)
    infer_instance
  have hcomp : ∀ U : Y.affineOpens,
      IsOpenImmersion (f.normalizationOpenCover.f U ≫ f.fromNormalization) := by
    intro U
    rw [Scheme.Hom.ι_fromNormalization]
    haveI := hpiece U
    haveI : IsOpenImmersion (Spec.map ((f.normalizationDiagramMap).app (Opposite.op U.1))) :=
      IsOpenImmersion.of_isIso _
    exact @IsOpenImmersion.comp _ _ _ _ _ this (IsAffineOpen.isOpenImmersion_fromSpec _)
  have hinj : Function.Injective f.fromNormalization := by
    intro z₁ z₂ h
    obtain ⟨V, hV, hyV, -⟩ := (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens)
      (show f.fromNormalization z₁ ∈ (⊤ : Y.Opens) from trivial)
    let U : Y.affineOpens := ⟨V, hV⟩
    have h₁ : z₁ ∈ f.fromNormalization ⁻¹ᵁ U.1 := hyV
    have h₂ : z₂ ∈ f.fromNormalization ⁻¹ᵁ U.1 := by
      show f.fromNormalization z₂ ∈ V
      rw [← h]; exact hyV
    rw [Scheme.Hom.fromNormalization_preimage] at h₁ h₂
    obtain ⟨q₁, rfl⟩ := h₁
    obtain ⟨q₂, rfl⟩ := h₂
    haveI := hcomp U
    congr 1
    apply (f.normalizationOpenCover.f U ≫ f.fromNormalization).isOpenEmbedding.injective
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h]
  haveI : IsOpenImmersion f.fromNormalization :=
    IsOpenImmersion.of_openCover_source _ f.normalizationOpenCover hinj hcomp
  haveI : Epi f.fromNormalization.base := by
    rw [TopCat.epi_iff_surjective]
    intro y
    obtain ⟨V, hV, hyV, -⟩ :=
      (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens) (show y ∈ (⊤ : Y.Opens) from trivial)
    let U : Y.affineOpens := ⟨V, hV⟩
    have hV' : IsAffineOpen V := hV
    haveI := hpiece U
    obtain ⟨p, hp⟩ : y ∈ Set.range hV'.fromSpec := by
      rw [← SetLike.mem_coe, ← hV'.range_fromSpec] at hyV; exact hyV
    obtain ⟨q, rfl⟩ := (Spec.map ((f.normalizationDiagramMap).app (Opposite.op U.1))).surjective p
    refine ⟨f.normalizationOpenCover.f U q, ?_⟩
    rw [← hp]
    exact (Scheme.Hom.comp_apply _ _ q).symm.trans
      ((congrArg (fun g => g q) (Scheme.Hom.ι_fromNormalization f U)).trans
        (Scheme.Hom.comp_apply _ _ q))
  exact IsOpenImmersion.isIso _

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in
private lemma isIso_stalkMap_of_comp_isOpenImmersion {W : Scheme.{u}} (f : X ⟶ Y) (c : W ⟶ X)
    [IsOpenImmersion c] (g : W ⟶ Y) [hg : IsOpenImmersion g] (h : c ≫ f = g) (w : W) :
    IsIso (f.stalkMap (c w)) := by
  subst h
  have h' := Scheme.Hom.stalkMap_comp c f w
  haveI : IsIso ((c ≫ f).stalkMap w) := inferInstance
  haveI : IsIso (f.stalkMap (c w) ≫ c.stalkMap w) := h' ▸ this
  exact IsIso.of_isIso_comp_right _ (c.stalkMap w)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

theorem _root_.GlobalTheory.birational_of_isIso_morphismRestrict (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] :
    IsDominant f ∧ IsIso (f.stalkMap (genericPoint X)) := by
  obtain ⟨y, hy⟩ := hU
  obtain ⟨x, -⟩ := (f ∣_ U).surjective ⟨y, hy⟩
  refine ⟨⟨?_⟩, ?_⟩
  · refine (U.isOpen.dense ⟨y, hy⟩).mono ?_
    intro z hz
    obtain ⟨w, hw⟩ := (f ∣_ U).surjective ⟨z, hz⟩
    exact ⟨w.1, by simpa using congrArg Subtype.val hw⟩
  · have hg : genericPoint X ∈ f ⁻¹ᵁ U :=
      ((genericPoint_spec X).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).2 ⟨x.1, trivial, x.2⟩
    simpa using isIso_stalkMap_of_comp_isOpenImmersion f (f ⁻¹ᵁ U).ι (f ∣_ U ≫ U.ι)
      (morphismRestrict_ι f U).symm ⟨_, hg⟩

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

theorem _root_.GlobalTheory.isOpenImmersion_of_quasiFinite_of_isIso_stalkMap (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsOpenImmersion f := by
  obtain ⟨U, hU, hpre⟩ := f.exists_isIso_morphismRestrict_toNormalization
  have hsurj : Function.Surjective (f.toNormalization ⁻¹ᵁ U).ι := by
    intro x
    have hx : x ∈ f.toNormalization ⁻¹ᵁ U := by
      show x ∈ (f.toNormalization ⁻¹ᵁ U).carrier
      rw [hpre]
      exact f.quasiFiniteAt x
    exact ⟨⟨x, hx⟩, rfl⟩
  haveI : IsIso (f.toNormalization ⁻¹ᵁ U).ι := by
    rw [isIso_iff_isOpenImmersion_and_epi_base, TopCat.epi_iff_surjective]
    exact ⟨inferInstance, hsurj⟩
  have h1 : IsOpenImmersion ((f.toNormalization ⁻¹ᵁ U).ι ≫ f.toNormalization) := by
    rw [← morphismRestrict_ι]
    infer_instance
  haveI : IsOpenImmersion f.toNormalization :=
    (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion _ _).mp h1
  haveI := _root_.GlobalTheory.isIso_fromNormalization_of_birational f hY
  rw [← f.toNormalization_fromNormalization]
  infer_instance

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

theorem _root_.GlobalTheory.isIso_of_isIntegralHom_of_isIso_stalkMap (f : X ⟶ Y) [IsIntegralHom f]
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsIso f := by
  haveI := _root_.GlobalTheory.isIso_fromNormalization_of_birational f hY
  rw [← f.toNormalization_fromNormalization]
  infer_instance

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

theorem _root_.GlobalTheory.isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap (f : X ⟶ Y) [IsProper f]
    [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y] [IsDominant f]
    [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsIso f := by
  haveI := _root_.GlobalTheory.isOpenImmersion_of_quasiFinite_of_isIso_stalkMap f hY
  haveI : Epi f.base := by
    rw [TopCat.epi_iff_surjective, ← Set.range_eq_univ]
    refine IsClopen.eq_univ ⟨f.isClosedMap.isClosed_range, f.isOpenEmbedding.isOpen_range⟩ ?_
    exact Set.range_nonempty _
  exact IsOpenImmersion.isIso f

theorem isOpenImmersion_of_quasiFinite_of_birational (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] : IsOpenImmersion f :=
  have ⟨_, _⟩ := birational_of_isIso_morphismRestrict f U hU
  isOpenImmersion_of_quasiFinite_of_isIso_stalkMap f hY

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

theorem _root_.GlobalTheory.isIso_of_isFinite_of_birational (f : X ⟶ Y) [IsFinite f]
    [IsIntegral X] [IsIntegral Y] (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] : IsIso f := by
  obtain ⟨hd, hs⟩ := _root_.GlobalTheory.birational_of_isIso_morphismRestrict f U hU
  exact _root_.GlobalTheory.isIso_of_isIntegralHom_of_isIso_stalkMap f hY

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

theorem _root_.GlobalTheory.isIso_of_isProper_of_quasiFinite_of_birational (f : X ⟶ Y) [IsProper f]
    [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] : IsIso f := by
  obtain ⟨hd, hs⟩ := _root_.GlobalTheory.birational_of_isIso_morphismRestrict f U hU
  exact _root_.GlobalTheory.isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap f hY

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in

theorem _root_.GlobalTheory.isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (V : X.Opens) (hV : Nonempty V) [IsOpenImmersion (V.ι ≫ f)] : IsOpenImmersion f := by
  obtain ⟨v, hv⟩ := hV
  have hg : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).2 ⟨v, trivial, hv⟩
  haveI : IsIso (f.stalkMap (genericPoint X)) := by
    simpa using isIso_stalkMap_of_comp_isOpenImmersion f V.ι (V.ι ≫ f) rfl ⟨_, hg⟩
  haveI : IsDominant f := by
    refine ⟨((V.ι ≫ f).isOpenEmbedding.isOpen_range.dense ⟨_, ⟨v, hv⟩, rfl⟩).mono ?_⟩
    rintro _ ⟨w, rfl⟩
    exact ⟨V.ι w, (Scheme.Hom.comp_apply _ _ w).symm⟩
  exact _root_.GlobalTheory.isOpenImmersion_of_quasiFinite_of_isIso_stalkMap f hY

theorem isOpenImmersion_and_isIso_of_quasiFinite_of_birational (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] :
    IsOpenImmersion f ∧ (IsFinite f → IsIso f) ∧ (IsProper f → IsIso f) :=
  ⟨isOpenImmersion_of_quasiFinite_of_birational f hY U hU,
    fun _ ↦ isIso_of_isFinite_of_birational f hY U hU,
    fun _ ↦ isIso_of_isProper_of_quasiFinite_of_birational f hY U hU⟩

end Normal

section Constructible

end Constructible

section Etale

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]

end Etale

end GlobalTheory
