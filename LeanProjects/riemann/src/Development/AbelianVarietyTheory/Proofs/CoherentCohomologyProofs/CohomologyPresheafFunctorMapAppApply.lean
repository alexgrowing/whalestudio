import Mathlib

open CategoryTheory Abelian Opposite Limits TopologicalSpace

universe w v u

namespace GlobalTheory
namespace Flasque

section Site

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

noncomputable abbrev freeSheaf (U : C) : Sheaf J AddCommGrpCat.{v} :=
  (presheafToSheaf J _).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

noncomputable abbrev freeSheafMap {V U : C} (i : V ⟶ U) : freeSheaf J V ⟶ freeSheaf J U :=
  (presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free)

instance mono_freeSheafMap {V U : C} (i : V ⟶ U) [Mono i] : Mono (freeSheafMap J i) := by
  infer_instance

noncomputable def freeSheafGen (U : C) : (freeSheaf J U).obj.obj (op U) :=
  (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U) (FreeAbelianGroup.of (𝟙 U))

variable {J}

noncomputable def freeSheafHomEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    (freeSheaf J U ⟶ F) ≃+ F.obj.obj (op U) where
  toEquiv := ((sheafificationAdjunction J _).homEquiv _ _).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans yonedaEquiv)
  map_add' f g := by
    rfl

lemma freeSheafHomEquiv_apply (U : C) (F : Sheaf J AddCommGrpCat.{v}) (f : freeSheaf J U ⟶ F) :
    freeSheafHomEquiv U F f = f.hom.app (op U) (freeSheafGen J U) := rfl

lemma freeSheafHomEquiv_comp {U : C} {F G : Sheaf J AddCommGrpCat.{v}} (f : freeSheaf J U ⟶ F)
    (g : F ⟶ G) :
    freeSheafHomEquiv U G (f ≫ g) = g.hom.app (op U) (freeSheafHomEquiv U F f) := rfl

lemma freeSheafMap_gen {V U : C} (i : V ⟶ U) :
    (freeSheafMap J i).hom.app (op V) (freeSheafGen J V) =
      (freeSheaf J U).obj.map i.op (freeSheafGen J U) := by
  have h1 := congr(($(toSheafify_naturality J
    (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free)).app (op V)) (FreeAbelianGroup.of (𝟙 V)))
  have h2 := congr($((toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).naturality i.op)
    (FreeAbelianGroup.of (𝟙 U)))
  refine h1.symm.trans (Eq.trans ?_ h2)
  change (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op V) (FreeAbelianGroup.of (𝟙 V ≫ i)) =
    (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op V) (FreeAbelianGroup.of (i ≫ 𝟙 U))
  simp

lemma freeSheafHomEquiv_freeSheafMap_comp {V U : C} (i : V ⟶ U) {F : Sheaf J AddCommGrpCat.{v}}
    (f : freeSheaf J U ⟶ F) :
    freeSheafHomEquiv V F (freeSheafMap J i ≫ f) = F.obj.map i.op (freeSheafHomEquiv U F f) := by
  rw [freeSheafHomEquiv_comp, freeSheafHomEquiv_apply, freeSheafMap_gen, freeSheafHomEquiv_apply]
  exact congr($(f.hom.naturality i.op) (freeSheafGen J U))

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

noncomputable def sectionsEquiv (F : Sheaf J AddCommGrpCat.{v}) (U : C) :
    F.H' 0 U ≃+ F.obj.obj (op U) :=
  (Ext.addEquiv₀ (X := freeSheaf J U) (Y := F)).trans (freeSheafHomEquiv U F)

lemma sectionsEquiv_mk₀ {F : Sheaf J AddCommGrpCat.{v}} {U : C} (f : freeSheaf J U ⟶ F) :
    sectionsEquiv F U (Ext.mk₀ f) = freeSheafHomEquiv U F f :=
  congrArg (freeSheafHomEquiv U F) (Ext.addEquiv₀.apply_symm_apply f)

lemma sectionsEquiv_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (U : C) (x : F.H' 0 U) :
    sectionsEquiv G U (((Sheaf.cohomologyPresheafFunctor J 0).map f).app (op U) x) =
      f.hom.app (op U) (sectionsEquiv F U x) := by
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (freeSheaf J U) F).2 x
  refine (congrArg (sectionsEquiv G U) (Ext.mk₀_comp_mk₀ g f)).trans ?_
  rw [sectionsEquiv_mk₀, sectionsEquiv_mk₀, freeSheafHomEquiv_comp]

lemma sectionsEquiv_restrict (F : Sheaf J AddCommGrpCat.{v}) {V U : C} (i : V ⟶ U)
    (x : F.H' 0 U) :
    sectionsEquiv F V ((F.cohomologyPresheaf 0).map i.op x) =
      F.obj.map i.op (sectionsEquiv F U x) := by
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (freeSheaf J U) F).2 x
  refine (congrArg (sectionsEquiv F V) (Ext.mk₀_comp_mk₀ (freeSheafMap J i) g)).trans ?_
  rw [sectionsEquiv_mk₀, sectionsEquiv_mk₀, freeSheafHomEquiv_freeSheafMap_comp]

open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] in
variable {J} in
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] in

lemma _root_.GlobalTheory.Flasque.subsingleton_H'_of_injective (I : Sheaf J AddCommGrpCat.{v}) [Injective I]
    (n : ℕ) (U : C) : Subsingleton (I.H' (n + 1) U) :=
  Ext.subsingleton_of_injective (_root_.GlobalTheory.Flasque.freeSheaf J U) I n

section Shift

variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

noncomputable def connecting (n : ℕ) (U : C) : S.X₃.H' n U →+ S.X₁.H' (n + 1) U :=
  hS.extClass.postcomp (freeSheaf J U) rfl

lemma exact_map_connecting (n : ℕ) (U : C) :
    Function.Exact (((Sheaf.cohomologyPresheafFunctor J n).map S.g).app (op U))
      (connecting hS n U) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.covariant_sequence_exact₃' (freeSheaf J U) hS n (n + 1) rfl)

lemma exact_connecting_map (n : ℕ) (U : C) :
    Function.Exact (connecting hS n U)
      (((Sheaf.cohomologyPresheafFunctor J (n + 1)).map S.f).app (op U)) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.covariant_sequence_exact₁' (freeSheaf J U) hS n (n + 1) rfl)

lemma connecting_naturality {T : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) (U : C) (x : S.X₃.H' n U) :
    connecting hT n U (((Sheaf.cohomologyPresheafFunctor J n).map φ.τ₃).app (op U) x) =
      ((Sheaf.cohomologyPresheafFunctor J (n + 1)).map φ.τ₁).app (op U) (connecting hS n U x) := by
  have key (y : Ext (freeSheaf J U) S.X₃ n) :
      (y.comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp hT.extClass rfl =
        (y.comp hS.extClass rfl).comp (Ext.mk₀ φ.τ₁) (add_zero (n + 1)) := by
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
      hS.extClass_naturality hT φ]
  exact key x

lemma connecting_restrict (n : ℕ) {V U : C} (i : V ⟶ U) (x : S.X₃.H' n U) :
    connecting hS n V ((S.X₃.cohomologyPresheaf n).map i.op x) =
      (S.X₁.cohomologyPresheaf (n + 1)).map i.op (connecting hS n U x) :=
  Ext.comp_assoc (Ext.mk₀ (freeSheafMap J i)) x hS.extClass (zero_add n) rfl (by lia)

lemma connecting_injective (n : ℕ) (U : C) (h : Subsingleton (S.X₂.H' n U)) :
    Function.Injective (connecting hS n U) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (exact_map_connecting hS n U x).1 hx
  rw [Subsingleton.elim y 0, map_zero]

lemma connecting_surjective (n : ℕ) (U : C) (h : Subsingleton (S.X₂.H' (n + 1) U)) :
    Function.Surjective (connecting hS n U) := fun x ↦
  (exact_connecting_map hS n U x).1 (Subsingleton.elim (h := h) _ _)

noncomputable def shiftEquiv (n : ℕ) (U : C) (h : Subsingleton (S.X₂.H' n U))
    (h' : Subsingleton (S.X₂.H' (n + 1) U)) : S.X₃.H' n U ≃+ S.X₁.H' (n + 1) U :=
  AddEquiv.ofBijective (connecting hS n U)
    ⟨connecting_injective hS n U h, connecting_surjective hS n U h'⟩

@[simp]
lemma shiftEquiv_apply (n : ℕ) (U : C) (h : Subsingleton (S.X₂.H' n U))
    (h' : Subsingleton (S.X₂.H' (n + 1) U)) (x : S.X₃.H' n U) :
    shiftEquiv hS n U h h' x = connecting hS n U x := rfl

noncomputable def connecting₀ (U : C) : S.X₃.obj.obj (op U) →+ S.X₁.H' 1 U :=
  (connecting hS 0 U).comp (sectionsEquiv S.X₃ U).symm.toAddMonoidHom

lemma connecting₀_apply (U : C) (s : S.X₃.obj.obj (op U)) :
    connecting₀ hS U s = connecting hS 0 U ((sectionsEquiv S.X₃ U).symm s) := rfl

lemma exact_app_connecting₀ (U : C) :
    Function.Exact (S.g.hom.app (op U)) (connecting₀ hS U) := by
  intro s
  obtain ⟨x, rfl⟩ := (sectionsEquiv S.X₃ U).surjective s
  rw [connecting₀_apply, AddEquiv.symm_apply_apply, exact_map_connecting hS 0 U x]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨sectionsEquiv S.X₂ U y, (sectionsEquiv_map S.g U y).symm⟩
  · rintro ⟨t, ht⟩
    obtain ⟨y, rfl⟩ := (sectionsEquiv S.X₂ U).surjective t
    exact ⟨y, (sectionsEquiv S.X₃ U).injective ((sectionsEquiv_map S.g U y).trans ht)⟩

lemma exact_connecting₀_map (U : C) :
    Function.Exact (connecting₀ hS U)
      (((Sheaf.cohomologyPresheafFunctor J 1).map S.f).app (op U)) := by
  intro x
  refine (exact_connecting_map hS 0 U x).trans ⟨?_, ?_⟩
  · rintro ⟨y, rfl⟩
    exact ⟨sectionsEquiv S.X₃ U y, by rw [connecting₀_apply, AddEquiv.symm_apply_apply]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩

lemma connecting₀_surjective (U : C) (h : Subsingleton (S.X₂.H' 1 U)) :
    Function.Surjective (connecting₀ hS U) :=
  (connecting_surjective hS 0 U h).comp (sectionsEquiv S.X₃ U).symm.surjective

lemma ker_connecting₀ (U : C) : (connecting₀ hS U).ker = (S.g.hom.app (op U)).hom.range :=
  AddSubgroup.ext fun s ↦ exact_app_connecting₀ hS U s

lemma connecting₀_naturality {T : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hT : T.ShortExact)
    (φ : S ⟶ T) (U : C) (s : S.X₃.obj.obj (op U)) :
    connecting₀ hT U (φ.τ₃.hom.app (op U) s) =
      ((Sheaf.cohomologyPresheafFunctor J 1).map φ.τ₁).app (op U) (connecting₀ hS U s) := by
  obtain ⟨x, rfl⟩ := (sectionsEquiv S.X₃ U).surjective s
  rw [← sectionsEquiv_map, connecting₀_apply, connecting₀_apply, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]
  exact connecting_naturality hS hT φ 0 U x

lemma connecting₀_restrict {V U : C} (i : V ⟶ U) (s : S.X₃.obj.obj (op U)) :
    connecting₀ hS V (S.X₃.obj.map i.op s) =
      (S.X₁.cohomologyPresheaf 1).map i.op (connecting₀ hS U s) := by
  obtain ⟨x, rfl⟩ := (sectionsEquiv S.X₃ U).surjective s
  rw [← sectionsEquiv_restrict, connecting₀_apply, connecting₀_apply, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]
  exact connecting_restrict hS 0 i x

noncomputable def cokerEquiv (U : C) (h : Subsingleton (S.X₂.H' 1 U)) :
    (S.X₃.obj.obj (op U) ⧸ (S.g.hom.app (op U)).hom.range) ≃+ S.X₁.H' 1 U :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_connecting₀ hS U).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (connecting₀_surjective hS U h))

@[simp]
lemma cokerEquiv_mk (U : C) (h : Subsingleton (S.X₂.H' 1 U)) (s : S.X₃.obj.obj (op U)) :
    cokerEquiv hS U h (QuotientAddGroup.mk s) = connecting₀ hS U s := rfl

end Shift

end Site

section Injective

variable {A : Type u} [Category.{v} A] [Abelian A]

noncomputable abbrev injectiveShortComplex [EnoughInjectives A] (F : A) : ShortComplex A :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)

open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {A : Type u} [Category.{v} A] [Abelian A] in
lemma _root_.GlobalTheory.Flasque.injectiveShortComplex_shortExact [EnoughInjectives A] (F : A) :
    (_root_.GlobalTheory.Flasque.injectiveShortComplex F).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {A : Type u} [Category.{v} A] [Abelian A] in

lemma _root_.GlobalTheory.Flasque.exists_hom_τ₁_eq {S T : ShortComplex A} (hS : S.ShortExact)
    [Injective T.X₂] (f : S.X₁ ⟶ T.X₁) : ∃ φ : S ⟶ T, φ.τ₁ = f := by
  have := hS.mono_f
  let τ₂ : S.X₂ ⟶ T.X₂ := Injective.factorThru (f ≫ T.f) S.f
  have h₂ : S.f ≫ τ₂ = f ≫ T.f := Injective.comp_factorThru _ _
  have hw : S.f ≫ τ₂ ≫ T.g = 0 := by
    rw [reassoc_of% h₂, T.zero, comp_zero]
  let τ₃ : S.X₃ ⟶ T.X₃ := hS.gIsCokernel.desc (CokernelCofork.ofπ _ hw)
  have h₃ : S.g ≫ τ₃ = τ₂ ≫ T.g :=
    hS.gIsCokernel.fac (CokernelCofork.ofπ _ hw) WalkingParallelPair.one
  exact ⟨{ τ₁ := f, τ₂ := τ₂, τ₃ := τ₃, comm₁₂ := h₂.symm, comm₂₃ := h₃.symm }, rfl⟩

end Injective

section Space

variable {X : TopCat.{u}}

open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] in
variable {J} in
private lemma freeSheafHomEquiv_eq_yonedaEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v})
    (h : _root_.GlobalTheory.Flasque.freeSheaf J U ⟶ F) :
    _root_.GlobalTheory.Flasque.freeSheafHomEquiv U F h = yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)
        ((sheafificationAdjunction J _).homEquiv _ _ h)) := rfl

open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] in
variable {J} in
private lemma freeSheafHomEquiv_freeSheafMap_comp' {V U : C} (i : V ⟶ U) (F : Sheaf J AddCommGrpCat.{v})
    (h : _root_.GlobalTheory.Flasque.freeSheaf J U ⟶ F) :
    _root_.GlobalTheory.Flasque.freeSheafHomEquiv V F (_root_.GlobalTheory.Flasque.freeSheafMap J i ≫ h) =
      F.obj.map i.op (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U F h) := by
  rw [freeSheafHomEquiv_eq_yonedaEquiv, freeSheafHomEquiv_eq_yonedaEquiv,
    Adjunction.homEquiv_naturality_left]
  erw [Adjunction.homEquiv_naturality_left]
  rw [← yonedaEquiv_naturality]
  rfl

open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {X : TopCat.{u}} in

theorem _root_.GlobalTheory.Flasque.isFlasque_of_injective (I : TopCat.Sheaf AddCommGrpCat.{u} X) [hI : Injective I] :
    I.IsFlasque := by
  let I' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := I
  haveI : Injective I' := hI
  refine ⟨fun {U V} i => ?_⟩
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  let g : _root_.GlobalTheory.Flasque.freeSheaf _ (unop V) ⟶ I' :=
    (_root_.GlobalTheory.Flasque.freeSheafHomEquiv (unop V) I').symm s
  let h : _root_.GlobalTheory.Flasque.freeSheaf _ (unop U) ⟶ I' :=
    Injective.factorThru g (_root_.GlobalTheory.Flasque.freeSheafMap _ i.unop)
  refine ⟨_root_.GlobalTheory.Flasque.freeSheafHomEquiv (unop U) I' h, ?_⟩
  have key := freeSheafHomEquiv_freeSheafMap_comp' i.unop I' h
  rw [Injective.comp_factorThru] at key
  simpa [g] using key.symm

instance isFlasque_injectiveShortComplex_X₂ (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (injectiveShortComplex F).X₂.IsFlasque :=
  isFlasque_of_injective _

lemma isFlasque_injectiveShortComplex_X₃ (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque] :
    (injectiveShortComplex F).X₃.IsFlasque :=
  TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ (injectiveShortComplex_shortExact F)

variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] in
variable {J} in
private lemma freeSheafHomEquiv_comp' (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (h : _root_.GlobalTheory.Flasque.freeSheaf J U ⟶ F) (f : F ⟶ G) :
    _root_.GlobalTheory.Flasque.freeSheafHomEquiv U G (h ≫ f) =
      f.hom.app (op U) (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U F h) := by
  rw [freeSheafHomEquiv_eq_yonedaEquiv, freeSheafHomEquiv_eq_yonedaEquiv,
    Adjunction.homEquiv_naturality_right]
  erw [Adjunction.homEquiv_naturality_right]
  rw [yonedaEquiv_comp]
  rfl

open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {X : TopCat.{u}} in
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in

theorem _root_.GlobalTheory.Flasque.subsingleton_H'_of_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [hF : F.IsFlasque] (n : ℕ) (U : Opens X) : Subsingleton (F.H' (n + 1) U) := by
  let Y : TopCat.Sheaf AddCommGrpCat.{u} X :=
    _root_.GlobalTheory.Flasque.freeSheaf (Opens.grothendieckTopology X) U
  letI : HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X) := ‹HasExt.{w} (Sheaf _ _)›
  suffices h : ∀ x : Ext.{w} Y F (n + 1), x = 0 from ⟨fun a b => (h a).trans (h b).symm⟩
  induction n generalizing F with
  | zero =>
    intro x
    have hS := _root_.GlobalTheory.Flasque.injectiveShortComplex_shortExact F
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ Y hS x (Ext.eq_zero_of_injective _) rfl
    obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surjective x₃
    have hepi := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) hS
    rw [AddCommGrpCat.epi_iff_surjective] at hepi
    obtain ⟨t, ht⟩ := hepi (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U _ φ)
    let ψ : Y ⟶ (_root_.GlobalTheory.Flasque.injectiveShortComplex F).X₂ :=
      (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U _).symm t
    have hψ : ψ ≫ (_root_.GlobalTheory.Flasque.injectiveShortComplex F).g = φ := by
      apply (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U _).injective
      refine (freeSheafHomEquiv_comp' U ψ (_root_.GlobalTheory.Flasque.injectiveShortComplex F).g).trans ?_
      simp only [ψ, AddEquiv.apply_symm_apply]
      exact ht
    rw [Ext.homEquiv₀_symm_apply, ← hψ, ← Ext.mk₀_comp_mk₀,
      Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (by simp), hS.comp_extClass, Ext.comp_zero]
  | succ m ih =>
    intro x
    have hS := _root_.GlobalTheory.Flasque.injectiveShortComplex_shortExact F
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ Y hS x (Ext.eq_zero_of_injective _) rfl
    haveI : (_root_.GlobalTheory.Flasque.injectiveShortComplex F).X₃.IsFlasque :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS
    rw [ih _ x₃, Ext.zero_comp]

open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {X : TopCat.{u}} in
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
theorem _root_.GlobalTheory.Flasque.subsingleton_H'_of_isFlasque_of_pos (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [F.IsFlasque] {n : ℕ} (hn : 0 < n) (U : Opens X) : Subsingleton (F.H' n U) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  exact _root_.GlobalTheory.Flasque.subsingleton_H'_of_isFlasque F m U

end Space

end Flasque

end GlobalTheory
