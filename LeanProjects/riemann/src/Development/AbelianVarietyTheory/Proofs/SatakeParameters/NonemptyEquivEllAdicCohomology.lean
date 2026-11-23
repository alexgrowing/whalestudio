import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Abelian

namespace GlobalTheory.Et.Small

universe w w' v₁ v₂ v₃ u₁ u₂ u₃

structure Good {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] (Φ : A ⥤ B) : Prop where
  lim : PreservesFiniteLimits Φ
  colim : PreservesFiniteColimits Φ
  inj : Φ.PreservesInjectiveObjects

theorem Good.comp {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {C : Type u₃} [Category.{v₃} C]
    {Φ : A ⥤ B} {Ψ : B ⥤ C} (h : Good Φ) (h' : Good Ψ) : Good (Φ ⋙ Ψ) := by
  obtain ⟨_, _, _⟩ := h
  obtain ⟨_, _, _⟩ := h'
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _, inferInstance⟩

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀ Ext.mapExactFunctor_extClass in
attribute [local instance] Ext.subsingleton_of_injective in

theorem ext_bijective {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasExt.{w} A] [EnoughInjectives A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasExt.{w'} B]
    (Φ : A ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] [Φ.PreservesInjectiveObjects]
    {Z : A} {Z' : B} (a : Z' ⟶ Φ.obj Z) (ha : ∀ F : A, Function.Bijective fun g : Z ⟶ F => a ≫ Φ.map g)
    (n : ℕ) (F : A) :
    Function.Bijective (((Ext.mk₀ a).precomp (Φ.obj F) (zero_add n)).comp (Φ.mapExtAddHom.{w, w'} Z F n)) := by
  induction n generalizing F with
  | zero =>
    rw [← Function.Bijective.of_comp_iff _ (Ext.mk₀_bijective Z F)]
    convert (Ext.mk₀_bijective Z' (Φ.obj F)).comp (ha F) using 1
    ext g
    simp
  | succ n hn =>
    let I : InjectivePresentation F := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective (S.map Φ).X₂ := Functor.PreservesInjectiveObjects.injective_obj I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (((Ext.mk₀ a).precomp (Φ.obj S.X₂) (zero_add n)).comp (Φ.mapExtAddHom.{w, w'} Z S.X₂ n))
      (((Ext.mk₀ a).precomp (Φ.obj S.X₃) (zero_add n)).comp (Φ.mapExtAddHom.{w, w'} Z S.X₃ n))
      (((Ext.mk₀ a).precomp (Φ.obj S.X₁) (zero_add (n + 1))).comp (Φ.mapExtAddHom.{w, w'} Z S.X₁ (n + 1)))
      (by
        ext x
        change ((Ext.mk₀ a).comp (x.mapExactFunctor Φ) (zero_add n)).comp (Ext.mk₀ (Φ.map S.g)) (add_zero n) =
          (Ext.mk₀ a).comp ((x.comp (Ext.mk₀ S.g) (add_zero n)).mapExactFunctor Φ) (zero_add n)
        rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero])
      (by
        ext x
        change ((Ext.mk₀ a).comp (x.mapExactFunctor Φ) (zero_add n)).comp (hS.map Φ).extClass rfl =
          (Ext.mk₀ a).comp ((x.comp hS.extClass rfl).mapExactFunctor Φ) (zero_add (n + 1))
        rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
        exact Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' Z hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' Z' (hS.map Φ) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ (hS.map Φ) y₁ (by subsingleton) rfl)

theorem nonempty_ext_equiv {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasExt.{w} A] [EnoughInjectives A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasExt.{w'} B]
    (Φ : A ⥤ B) (h : Good Φ) {Z : A} {Z' : B} (e : ∀ F : A, (Z ⟶ F) ≃ (Z' ⟶ Φ.obj F))
    (he : ∀ {F G : A} (g : Z ⟶ F) (f : F ⟶ G), e G (g ≫ f) = e F g ≫ Φ.map f)
    (n : ℕ) (F : A) (F' : B) (i : Φ.obj F ≅ F') : Nonempty (Ext.{w} Z F n ≃+ Ext.{w'} Z' F' n) := by
  obtain ⟨_, _, _⟩ := h
  have : Φ.Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts Φ
    exact Functor.additive_of_preservesBinaryBiproducts _
  have hb := ext_bijective.{w, w'} Φ (e Z (𝟙 Z)) (fun F => by
    convert (e F).bijective using 1
    ext g
    rw [← he, Category.id_comp]) n F
  exact ⟨(AddEquiv.ofBijective _ hb).trans
    (((extFunctor.{w'} n).obj (op Z')).mapIso i).addCommGroupIsoToAddEquiv⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

theorem lan_preservesFiniteLimits {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (E : Type u₃) [Category.{v₃} E] [HasFiniteLimits E] (F : C ⥤ D)
    [∀ X : D, HasColimitsOfShape (CostructuredArrow F X) E]
    (h : ∀ X : D, HasExactColimitsOfShape (CostructuredArrow F X) E) :
    PreservesFiniteLimits (F.lan : (C ⥤ E) ⥤ D ⥤ E) := by
  have e (X : D) : F.lan ⋙ (evaluation D E).obj X ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
    NatIso.ofComponents (fun G =>
      IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
      (colimit.isColimit _)) (fun {G₁ G₂} φ => by
        apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
        intro T
        have h₁ := fun (G : C ⥤ E) => IsColimit.comp_coconePointUniqueUpToIso_hom
          (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X) (colimit.isColimit _) T
        have h₂ := congr_app (F.lanUnit.naturality φ) T.left
        dsimp at h₁ h₂ ⊢
        simp only [Category.assoc] at h₁ ⊢
        simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
        rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
          ι_colimMap, Functor.whiskerLeft_app]
        rfl)
  constructor
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation (F.lan : (C ⥤ E) ⥤ D ⥤ E) J
  intro K
  have := (h K).preservesFiniteLimits
  exact preservesLimitsOfShape_of_natIso (e K).symm

theorem good_pushforward {C : Type 1} [Category.{0} C] {D : Type 1} [Category.{0} D] (G : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [G.IsContinuous J K] [G.IsCocontinuous J K]
    (h : ∀ X : Dᵒᵖ, HasExactColimitsOfShape (CostructuredArrow G.op X) Ab.{1}) :
    Good (G.sheafPushforwardContinuous Ab.{1} J K) := by
  have := lan_preservesFiniteLimits Ab.{1} G.op h
  have adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{1} J K
  have := adj.isRightAdjoint
  have := (G.sheafAdjunctionCocontinuous Ab.{1} J K).isLeftAdjoint
  have : (Functor.sheafPullbackConstruction.sheafPullback G Ab.{1} J K).PreservesMonomorphisms := by
    unfold Functor.sheafPullbackConstruction.sheafPullback
    infer_instance
  exact ⟨inferInstance, inferInstance,
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj⟩

def sliceDiscrete {C : Type u₁} [Category.{v₁} C] (X : C) (U : Cᵒᵖ) :
    Discrete (U.unop ⟶ X) ⥤ CostructuredArrow (Over.forget X).op U :=
  Discrete.functor fun f => CostructuredArrow.mk (Y := op (Over.mk f)) (𝟙 U)

theorem final_sliceDiscrete {C : Type u₁} [Category.{v₁} C] (X : C) (U : Cᵒᵖ) : (sliceDiscrete X U).Final where
  out T := by
    have key (f : U.unop ⟶ X) (φ : T ⟶ (sliceDiscrete X U).obj ⟨f⟩) : φ.left.unop.left = T.hom.unop := by
      have := congrArg Quiver.Hom.unop (CostructuredArrow.w φ)
      exact (Category.id_comp _).symm.trans this
    have : Nonempty (StructuredArrow T (sliceDiscrete X U)) :=
      ⟨StructuredArrow.mk (Y := ⟨T.hom.unop ≫ T.left.unop.hom⟩)
        (CostructuredArrow.homMk (Over.homMk (U := Over.mk _) T.hom.unop rfl).op (Category.comp_id _))⟩
    refine zigzag_isConnected fun j₁ j₂ => ?_
    obtain ⟨⟨⟨⟩⟩, ⟨f₁⟩, φ₁⟩ := j₁
    obtain ⟨⟨⟨⟩⟩, ⟨f₂⟩, φ₂⟩ := j₂
    have h₁ : f₁ = T.hom.unop ≫ T.left.unop.hom := by
      rw [← key f₁ φ₁]; exact (Over.w φ₁.left.unop).symm
    have h₂ : f₂ = T.hom.unop ≫ T.left.unop.hom := by
      rw [← key f₂ φ₂]; exact (Over.w φ₂.left.unop).symm
    obtain rfl : f₁ = f₂ := h₁.trans h₂.symm
    obtain rfl : φ₁ = φ₂ := by
      apply CostructuredArrow.hom_ext
      apply Quiver.Hom.unop_inj
      apply Over.OverMorphism.ext
      exact (key f₁ φ₁).trans (key f₁ φ₂).symm
    exact Zigzag.refl _

theorem good_over {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C) (X : C) :
    Good ((Over.forget X).sheafPushforwardContinuous Ab.{1} (J.over X) J) := by
  refine good_pushforward _ _ _ fun U => ?_
  have := final_sliceDiscrete X U
  have : AB4OfSize.{0} Ab.{1} := AB4OfSize_shrink.{0, 1} _
  exact hasExactColimitsOfShape_of_final _ (sliceDiscrete X U)

set_option backward.isDefEq.respectTransparency.types false in
theorem good_small (X : Scheme.{0}) :
    Good ((Scheme.ProEt.forget X).sheafPushforwardContinuous Ab.{1} (Scheme.ProEt.topology X)
      (Scheme.proetaleTopology.over X)) := by
  have : (Scheme.ProEt.forget X).IsCocontinuous (Scheme.ProEt.topology X) (Scheme.proetaleTopology.over X) := by
    have h : Scheme.ProEt.topology X =
        (Scheme.ProEt.forget X).restrictedTopology (Scheme.proetaleTopology.over X) :=
      MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology _
        Scheme.proetalePrecoverage_le_precoverage_weaklyEtale
    rw [h]
    infer_instance
  refine good_pushforward _ _ _ fun U => ?_
  have : AB5OfSize.{0, 1} Ab.{1} := AB5OfSize_of_univLE.{0, 1, 1, 1} _
  infer_instance

theorem good_forget {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C) (S : Type 1) [CommRing S]
    [Module.Flat ℤ S] [HasSheafify J (ModuleCat.{1} S)] : Good (sheafCompose J (forget₂ (ModuleCat.{1} S) Ab.{1})) := by
  let e : ℤ ≃+* ULift.{1} ℤ := ULift.ringEquiv.symm
  let f : ULift.{1} ℤ →+* S := (Int.castRingHom S).comp e.symm.toRingHom
  have hf : f.Flat := RingHom.Flat.comp (RingHom.Flat.of_bijective e.symm.bijective)
    ((RingHom.flat_algebraMap_iff (R := ℤ) (S := S)).2 inferInstance)
  let V : ModuleCat.{1} (ULift.{1} ℤ) ⥤ Ab.{1} := ModuleCat.restrictScalars e.toRingHom ⋙ forget₂ (ModuleCat.{1} ℤ) Ab.{1}
  have : V.IsEquivalence := Functor.isEquivalence_trans _ _
  let i : ModuleCat.restrictScalars.{1} f ⋙ V ≅ forget₂ (ModuleCat.{1} S) Ab.{1} := Iso.refl _
  have adj : V.asEquivalence.inverse ⋙ ModuleCat.extendScalars.{1, 1, 1} f ⊣ forget₂ (ModuleCat.{1} S) Ab.{1} :=
    (V.asEquivalence.symm.toAdjunction.comp (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} f)).ofNatIsoRight i
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  have : (forget₂ (ModuleCat.{1} S) Ab.{1}).IsLeftAdjoint :=
    (((ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} f).comp V.asEquivalence.toAdjunction).ofNatIsoLeft i).isLeftAdjoint
  have adj' := Sheaf.adjunction J adj
  have := adj'.isRightAdjoint
  have : PreservesFiniteLimits (V.asEquivalence.inverse ⋙ ModuleCat.extendScalars.{1, 1, 1} f) :=
    comp_preservesFiniteLimits _ _
  have : (Sheaf.composeAndSheafify J
      (V.asEquivalence.inverse ⋙ ModuleCat.extendScalars.{1, 1, 1} f)).PreservesMonomorphisms := by
    generalize V.asEquivalence.inverse ⋙ ModuleCat.extendScalars.{1, 1, 1} f = G at this
    have : PreservesLimitsOfShape WalkingCospan ((Functor.whiskeringRight Cᵒᵖ _ _).obj G) := inferInstance
    have : ((Functor.whiskeringRight Cᵒᵖ _ _).obj G).PreservesMonomorphisms := inferInstance
    infer_instance
  let j : sheafCompose J (forget₂ (ModuleCat.{1} S) Ab.{1}) ≅
      Sheaf.composeAndSheafify J (forget₂ (ModuleCat.{1} S) Ab.{1}) :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ (sheafificationNatIso J Ab.{1})
  exact ⟨inferInstance, preservesFiniteColimits_of_natIso j.symm,
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj'⟩

variable (R : Type) [CommRing R]

def restrict (X : Scheme.{0}) : Shv R ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{1} :=
  sheafCompose _ (forget₂ (ModuleCat.{1} (ULift.{1} R)) Ab.{1}) ⋙
    (Over.forget X).sheafPushforwardContinuous Ab.{1} (Scheme.proetaleTopology.over X) Scheme.proetaleTopology ⋙
    (Scheme.ProEt.forget X).sheafPushforwardContinuous Ab.{1} (Scheme.ProEt.topology X) (Scheme.proetaleTopology.over X)

theorem good_restrict [Module.Flat ℤ R] (X : Scheme.{0}) : Good (restrict R X) :=
  (good_forget _ _).comp ((good_over _ X).comp (good_small X))

def freeOnEquiv (X : Scheme.{0}) (F : Shv R) : ((freeOn R).obj X ⟶ F) ≃ F.obj.obj (op X) :=
  ((sheafificationAdjunction _ _).homEquiv _ F).trans
    (((((ModuleCat.adj (ULift.{1} R)).whiskerRight Scheme.{0}ᵒᵖ)).homEquiv (uliftYoneda.{1}.obj X) F.obj).trans
      uliftYonedaEquiv)

theorem freeOnEquiv_comp (X : Scheme.{0}) {F G : Shv R} (g : (freeOn R).obj X ⟶ F) (f : F ⟶ G) :
    freeOnEquiv R X G (g ≫ f) = f.hom.app (op X) (freeOnEquiv R X F g) := rfl

set_option backward.isDefEq.respectTransparency.types false in

def isTerminalId (X : Scheme.{0}) : IsTerminal (Scheme.ProEt.mk (𝟙 X)) :=
  MorphismProperty.Over.mkIdTerminal @WeaklyEtale X

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem isSheaf_coefPre : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (coefPre R) := by
  refine (Presheaf.isSheaf_iff_isSheaf_forget Scheme.proetaleTopology.{0} (coefPre R)
    (forget (ModuleCat.{1} (ULift.{1} R)))).2 ?_
  change Presheaf.IsSheaf _ (continuousMapPresheaf R ⋙ uliftFunctor.{1})
  rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff, ← isSheaf_iff_isSheaf_of_type]
  exact .of_le Scheme.proetaleTopology_le_fpqcTopology (isSheaf_fpqcTopology_continuousMapPresheaf R)

theorem nonempty_equiv_ellAdicCohomology (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℕ) :
    Nonempty (H ℤ_[l] n X ≃+ X.EllAdicCohomology l n) := by
  let i : (restrict ℤ_[l] X).obj (coef ℤ_[l]) ≅
      (sheafCompose _ AddCommGrpCat.uliftFunctor.{1}).obj (X.ellAdicSheaf l) :=
    ((restrict ℤ_[l] X).mapIso (sheafificationIso ⟨coefPre ℤ_[l], isSheaf_coefPre ℤ_[l]⟩)).symm ≪≫ Iso.refl _
  let e' (G : Sheaf (Scheme.ProEt.topology X) Ab.{1}) :
      ((constantSheaf _ Ab.{1}).obj (AddCommGrpCat.of (ULift.{1} ℤ)) ⟶ G) ≃ G.obj.obj (op (Scheme.ProEt.mk (𝟙 X))) :=
    ((constantSheafAdj _ Ab.{1} (isTerminalId X)).homEquiv _ G).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv
  have he' {G G' : Sheaf (Scheme.ProEt.topology X) Ab.{1}} (g : _ ⟶ G) (f : G ⟶ G') :
      e' G' (g ≫ f) = f.hom.app _ (e' G g) := rfl
  refine nonempty_ext_equiv.{1, 1} (restrict ℤ_[l] X) (good_restrict _ X)
    (fun F => (freeOnEquiv ℤ_[l] X F).trans (e' ((restrict ℤ_[l] X).obj F)).symm) ?_ n _ _ i
  intro F G g f
  apply (e' _).injective
  rw [he']
  simp only [Equiv.trans_apply]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact freeOnEquiv_comp _ X g f

end GlobalTheory.Et.Small

end
