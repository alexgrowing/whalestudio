import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Limits Opposite Abelian

universe w' v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section ExtIso

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasExt.{w'} 𝒜]

noncomputable def extAddEquivOfIsoLeft {X X' : 𝒜} (e : X ≅ X') (Y : 𝒜) (n : ℕ) :
    Ext X Y n ≃+ Ext X' Y n where
  toFun x := (Ext.mk₀ e.inv).comp x (zero_add n)
  invFun x := (Ext.mk₀ e.hom).comp x (zero_add n)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp [Ext.comp_add]

end ExtIso

section Terminal

noncomputable def freeYonedaTerminalIso {T : C} (hT : IsTerminal T) :
    yoneda.obj T ⋙ AddCommGrpCat.free.{v} ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  NatIso.ofComponents (fun X =>
    letI : Unique (X.unop ⟶ T) := ⟨⟨hT.from _⟩, fun _ => hT.hom_ext _ _⟩
    ((FreeAbelianGroup.uniqueEquiv (X.unop ⟶ T)).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun {X Y} f => by
      ext x
      change ULift.up (FreeAbelianGroup.lift (fun _ => (1 : ℤ))
          (FreeAbelianGroup.map (fun g => f.unop ≫ g) x)) =
        ULift.up (FreeAbelianGroup.lift (fun _ => (1 : ℤ)) x)
      congr 1
      induction x using FreeAbelianGroup.induction_on with
      | zero => simp
      | of a => simp
      | neg a h => simp only [map_neg, h]
      | add a b ha hb => simp only [map_add, ha, hb])

variable [HasSheafify J AddCommGrpCat.{v}]

noncomputable def freeSheafTerminalIso {T : C} (hT : IsTerminal T) :
    (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj T ⋙ AddCommGrpCat.free) ≅
      (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  (presheafToSheaf J AddCommGrpCat.{v}).mapIso (freeYonedaTerminalIso hT)

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

noncomputable def cohomologyPresheafTerminalAddEquiv (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    {T : C} (hT : IsTerminal T) :
    (F.cohomologyPresheaf n).obj (op T) ≃+ Sheaf.H F n :=
  extAddEquivOfIsoLeft (freeSheafTerminalIso (J := J) hT) F n

end Terminal

section Zero

noncomputable def freeYonedaHomAddEquiv (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (yoneda.obj U ⋙ AddCommGrpCat.free.{v} ⟶ P) ≃+ P.obj (op U) where
  toEquiv := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) P).trans yonedaEquiv
  map_add' _ _ := rfl

lemma freeYonedaHomAddEquiv_apply (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (g : yoneda.obj U ⋙ AddCommGrpCat.free.{v} ⟶ P) :
    freeYonedaHomAddEquiv U P g = g.app (op U) (FreeAbelianGroup.of (𝟙 U)) := rfl

lemma freeYonedaHomAddEquiv_naturality_left {U V : C} (f : U ⟶ V) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (g : yoneda.obj V ⋙ AddCommGrpCat.free.{v} ⟶ P) :
    freeYonedaHomAddEquiv U P (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free ≫ g) =
      P.map f.op (freeYonedaHomAddEquiv V P g) := by
  change yonedaEquiv (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) P)
      (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (yoneda.map f) ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_left, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  have := NatTrans.naturality_apply
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj V) P) g) f.op (𝟙 V)
  exact (congrArg _ (Category.comp_id f).symm).trans this

variable [HasSheafify J AddCommGrpCat.{v}]

noncomputable abbrev freeSheaf (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]
    (U : C) : Sheaf J AddCommGrpCat.{v} :=
  (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

noncomputable abbrev freeSheafMap (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]
    {U V : C} (f : U ⟶ V) : freeSheaf J U ⟶ freeSheaf J V :=
  (presheafToSheaf J AddCommGrpCat.{v}).map
    (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free)

noncomputable def freeSheafHomAddEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    (freeSheaf J U ⟶ F) ≃+ F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat.{v}).homAddEquiv _ F).trans
    (freeYonedaHomAddEquiv U F.obj)

lemma freeSheafHomAddEquiv_naturality (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (g : freeSheaf J U ⟶ F) (φ : F ⟶ G) :
    freeSheafHomAddEquiv U G (g ≫ φ) = φ.hom.app (op U) (freeSheafHomAddEquiv U F g) := by
  simp only [freeSheafHomAddEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    freeYonedaHomAddEquiv_apply, Adjunction.homEquiv_naturality_right]
  rfl

lemma freeSheafHomAddEquiv_naturality_left {U V : C} (f : U ⟶ V) (F : Sheaf J AddCommGrpCat.{v})
    (g : freeSheaf J V ⟶ F) :
    freeSheafHomAddEquiv U F (freeSheafMap J f ≫ g) =
      F.obj.map f.op (freeSheafHomAddEquiv V F g) := by
  simp only [freeSheafHomAddEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    Adjunction.homEquiv_naturality_left]
  exact freeYonedaHomAddEquiv_naturality_left f F.obj _

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

noncomputable def H'.equiv₀ (F : Sheaf J AddCommGrpCat.{v}) (U : C) :
    F.H' 0 U ≃+ F.obj.obj (op U) :=
  (Ext.addEquiv₀ (X := freeSheaf J U) (Y := F)).trans (freeSheafHomAddEquiv U F)

lemma cohomologyPresheafFunctor_map_app_apply {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G)
    (n : ℕ) (U : C) (x : F.H' n U) :
    ((Sheaf.cohomologyPresheafFunctor J n).map φ).app (op U) x =
      (show Ext (freeSheaf J U) F n from x).comp (Ext.mk₀ φ) (add_zero n) := rfl

lemma H'.equiv₀_naturality {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G) (U : C)
    (x : F.H' 0 U) :
    H'.equiv₀ G U (((Sheaf.cohomologyPresheafFunctor J 0).map φ).app (op U) x) =
      φ.hom.app (op U) (H'.equiv₀ F U x) := by
  rw [cohomologyPresheafFunctor_map_app_apply]
  obtain ⟨g, rfl⟩ := (Ext.addEquiv₀ (X := freeSheaf J U) (Y := F)).symm.surjective x
  change freeSheafHomAddEquiv U G (Ext.addEquiv₀ ((Ext.addEquiv₀.symm g).comp (Ext.mk₀ φ)
      (add_zero 0))) = φ.hom.app (op U) (freeSheafHomAddEquiv U F
        (Ext.addEquiv₀ (Ext.addEquiv₀.symm g)))
  rw [AddEquiv.apply_symm_apply, ← freeSheafHomAddEquiv_naturality, Ext.addEquiv₀_symm_apply,
    Ext.mk₀_comp_mk₀]
  congr 1
  apply (Ext.mk₀_bijective _ _).injective
  simp

end Zero

section Injective

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

lemma H.eq_zero_of_injective (F : Sheaf J AddCommGrpCat.{v}) [Injective F] {n : ℕ}
    (x : Sheaf.H F (n + 1)) : x = 0 :=
  Ext.eq_zero_of_injective x

instance H'.subsingleton_of_injective (F : Sheaf J AddCommGrpCat.{v}) [Injective F] (n : ℕ)
    (U : C) : Subsingleton (F.H' (n + 1) U) :=
  subsingleton_of_forall_eq 0 fun x =>
    Ext.eq_zero_of_injective (show Ext (freeSheaf J U) F (n + 1) from x)

end Injective

section LongExact

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

noncomputable def H.δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : Sheaf.H S.X₃ n₀ →+ Sheaf.H S.X₁ n₁ :=
  hS.extClass.postcomp _ h

lemma H.δ_apply (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₃ n₀) :
    H.δ hS n₀ n₁ h x = x.comp hS.extClass h := rfl

noncomputable def H.sequence (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{w'} 5 :=
  ComposableArrows.mk₅ ((Sheaf.functorH J n₀).map S.f) ((Sheaf.functorH J n₀).map S.g)
    (AddCommGrpCat.ofHom (H.δ hS n₀ n₁ h)) ((Sheaf.functorH J n₁).map S.f)
    ((Sheaf.functorH J n₁).map S.g)

include hS in

theorem H.exact₂ {n : ℕ} (y : Sheaf.H S.X₂ n) (hy : Sheaf.H.map S.g n y = 0) :
    ∃ x : Sheaf.H S.X₁ n, Sheaf.H.map S.f n x = y :=
  Ext.covariant_sequence_exact₂ _ hS y hy

theorem H.exact₃ {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (y : Sheaf.H S.X₃ n₀)
    (hy : H.δ hS n₀ n₁ h y = 0) : ∃ x : Sheaf.H S.X₂ n₀, Sheaf.H.map S.g n₀ x = y :=
  Ext.covariant_sequence_exact₃ _ hS y h hy

theorem H.exact₁ {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₁ n₁)
    (hx : Sheaf.H.map S.f n₁ x = 0) : ∃ y : Sheaf.H S.X₃ n₀, H.δ hS n₀ n₁ h y = x :=
  Ext.covariant_sequence_exact₁ _ hS x hx h

lemma H.map_g_map_f {n : ℕ} (x : Sheaf.H S.X₁ n) :
    Sheaf.H.map S.g n (Sheaf.H.map S.f n x) = 0 := by
  rw [← Sheaf.H.map_comp_apply, S.zero, Sheaf.H.map_apply, Ext.mk₀_zero, Ext.comp_zero]

lemma H.δ_map_g {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₂ n₀) :
    H.δ hS n₀ n₁ h (Sheaf.H.map S.g n₀ x) = 0 := by
  rw [H.δ_apply, Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
    Ext.comp_zero]

lemma H.map_f_δ {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₃ n₀) :
    Sheaf.H.map S.f n₁ (H.δ hS n₀ n₁ h x) = 0 := by
  rw [H.δ_apply, Sheaf.H.map_apply, Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp,
    Ext.comp_zero]

noncomputable def H'.δ (U : C) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : S.X₃.H' n₀ U ⟶ S.X₁.H' n₁ U :=
  AddCommGrpCat.ofHom (hS.extClass.postcomp (freeSheaf J U) h)

noncomputable def H'.sequence (U : C) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{w'} 5 :=
  ComposableArrows.mk₅ (((Sheaf.cohomologyPresheafFunctor J n₀).map S.f).app (op U))
    (((Sheaf.cohomologyPresheafFunctor J n₀).map S.g).app (op U)) (H'.δ hS U n₀ n₁ h)
    (((Sheaf.cohomologyPresheafFunctor J n₁).map S.f).app (op U))
    (((Sheaf.cohomologyPresheafFunctor J n₁).map S.g).app (op U))

end LongExact

end GroundTheory.Arith.SchemeCoh
