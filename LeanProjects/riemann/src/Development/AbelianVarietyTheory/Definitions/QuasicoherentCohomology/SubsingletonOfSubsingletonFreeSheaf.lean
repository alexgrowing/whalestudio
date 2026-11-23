import Mathlib

open CategoryTheory Opposite Limits Abelian

universe w v u

noncomputable section

namespace GlobalTheory.SiteCoh

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

abbrev freeSheaf : C ⥤ Sheaf J AddCommGrpCat.{v} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙ presheafToSheaf _ _

def tautSection (U : C) : ((freeSheaf J).obj U).obj.obj (op U) :=
  (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U) (FreeAbelianGroup.of (𝟙 U))

variable {J}

def freeSheafHomEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    ((freeSheaf J).obj U ⟶ F) ≃+ F.obj.obj (op U) where
  toEquiv := ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) F.obj).trans yonedaEquiv)
  map_add' _ _ := rfl

lemma freeSheafHomEquiv_comp (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (φ : (freeSheaf J).obj U ⟶ F) (f : F ⟶ G) :
    freeSheafHomEquiv U G (φ ≫ f) = f.hom.app (op U) (freeSheafHomEquiv U F φ) := rfl

lemma freeSheaf_map_tautSection {U V : C} (i : V ⟶ U) :
    ((freeSheaf J).map i).hom.app (op V) (tautSection J V) =
      ((freeSheaf J).obj U).obj.map i.op (tautSection J U) := by
  have h₁ := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality J (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free.{v})) (op V))
    (FreeAbelianGroup.of (𝟙 V))
  have h₂ := ConcreteCategory.congr_hom
    ((toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free.{v})).naturality i.op)
    (FreeAbelianGroup.of (𝟙 U))
  refine h₁.symm.trans (Eq.trans ?_ h₂)
  change (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free.{v})).app (op V)
      (FreeAbelianGroup.of (𝟙 V ≫ i)) =
    (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free.{v})).app (op V)
      (FreeAbelianGroup.of (i ≫ 𝟙 U))
  rw [Category.id_comp, Category.comp_id]

lemma freeSheafHomEquiv_map_comp {U V : C} (i : V ⟶ U) {F : Sheaf J AddCommGrpCat.{v}}
    (φ : (freeSheaf J).obj U ⟶ F) :
    freeSheafHomEquiv V F ((freeSheaf J).map i ≫ φ) =
      F.obj.map i.op (freeSheafHomEquiv U F φ) := by
  change φ.hom.app (op V) (((freeSheaf J).map i).hom.app (op V) (tautSection J V)) = _
  rw [freeSheaf_map_tautSection]
  exact ConcreteCategory.congr_hom (φ.hom.naturality i.op) _

def freePresheafIsoConst {T : C} (hT : IsTerminal T) :
    yoneda.obj T ⋙ AddCommGrpCat.free.{v} ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  NatIso.ofComponents
    (fun V ↦
      letI : Unique (V.unop ⟶ T) := ⟨⟨hT.from _⟩, fun _ ↦ hT.hom_ext _ _⟩
      ((FreeAbelianGroup.uniqueEquiv (V.unop ⟶ T)).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun {V W} f ↦ by
      apply AddCommGrpCat.hom_ext
      apply FreeAbelianGroup.lift_ext
      intro x
      rfl)

def freeSheafIsoConst {T : C} (hT : IsTerminal T) :
    (freeSheaf J).obj T ≅ (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ)) :=
  (presheafToSheaf J _).mapIso (freePresheafIsoConst hT)

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

def extEquiv (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C) :
    F.H' n U ≃+ Ext.{w} ((freeSheaf J).obj U) F n :=
  AddEquiv.refl _

abbrev map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) (U : C) :
    F.H' n U ⟶ G.H' n U :=
  ((Sheaf.cohomologyPresheafFunctor J n).map f).app (op U)

abbrev res (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U V : C} (i : V ⟶ U) :
    F.H' n U ⟶ F.H' n V :=
  (F.cohomologyPresheaf n).map i.op

lemma extEquiv_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) (U : C)
    (x : F.H' n U) :
    extEquiv G n U (map f n U x) = (extEquiv F n U x).comp (Ext.mk₀ f) (add_zero n) := rfl

lemma extEquiv_res (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U V : C} (i : V ⟶ U)
    (x : F.H' n U) :
    extEquiv F n V (res F n i x) =
      (Ext.mk₀ ((freeSheaf J).map i)).comp (extEquiv F n U x) (zero_add n) := rfl

instance cohomologyPresheafFunctor_additive (n : ℕ) :
    (Sheaf.cohomologyPresheafFunctor.{w} J n).Additive where
  map_add {F G f g} := by
    ext U x
    apply (extEquiv G n U.unop).injective
    change (extEquiv F n U.unop x).comp (Ext.mk₀ (f + g)) (add_zero n) =
      (extEquiv F n U.unop x).comp (Ext.mk₀ f) (add_zero n) +
        (extEquiv F n U.unop x).comp (Ext.mk₀ g) (add_zero n)
    rw [Ext.mk₀_add, Ext.comp_add]

def zeroEquiv (F : Sheaf J AddCommGrpCat.{v}) (U : C) : F.H' 0 U ≃+ F.obj.obj (op U) :=
  (extEquiv F 0 U).trans (Ext.addEquiv₀.trans (freeSheafHomEquiv U F))

lemma zeroEquiv_mk₀ (F : Sheaf J AddCommGrpCat.{v}) (U : C) (φ : (freeSheaf J).obj U ⟶ F) :
    zeroEquiv F U ((extEquiv F 0 U).symm (Ext.mk₀ φ)) = freeSheafHomEquiv U F φ := by
  simp only [zeroEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  congr 1
  exact Ext.addEquiv₀.apply_symm_apply φ

lemma zeroEquiv_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (U : C) (x : F.H' 0 U) :
    zeroEquiv G U (map f 0 U x) = f.hom.app (op U) (zeroEquiv F U x) := by
  obtain ⟨y, rfl⟩ := (extEquiv F 0 U).symm.surjective x
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  rw [zeroEquiv_mk₀, ← freeSheafHomEquiv_comp, ← zeroEquiv_mk₀]
  congr 1
  apply (extEquiv G 0 U).injective
  rw [extEquiv_map, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, Ext.mk₀_comp_mk₀]

lemma zeroEquiv_res (F : Sheaf J AddCommGrpCat.{v}) {U V : C} (i : V ⟶ U) (x : F.H' 0 U) :
    zeroEquiv F V (res F 0 i x) = F.obj.map i.op (zeroEquiv F U x) := by
  obtain ⟨y, rfl⟩ := (extEquiv F 0 U).symm.surjective x
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  rw [zeroEquiv_mk₀, ← freeSheafHomEquiv_map_comp, ← zeroEquiv_mk₀]
  congr 1
  apply (extEquiv F 0 V).injective
  rw [extEquiv_res, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, Ext.mk₀_comp_mk₀]

def terminalEquiv (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {T : C} (hT : IsTerminal T) :
    F.H' n T ≃+ F.H n :=
  (extEquiv F n T).trans
    (((extFunctor n).mapIso (freeSheafIsoConst (J := J) hT).symm.op).app F).addCommGroupIsoToAddEquiv

lemma terminalEquiv_apply (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {T : C} (hT : IsTerminal T)
    (x : F.H' n T) :
    terminalEquiv F n hT x =
      (Ext.mk₀ (freeSheafIsoConst hT).inv).comp (extEquiv F n T x) (zero_add n) := rfl

lemma terminalEquiv_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) {T : C}
    (hT : IsTerminal T) (x : F.H' n T) :
    terminalEquiv G n hT (map f n T x) = Sheaf.H.map f n (terminalEquiv F n hT x) := by
  rw [terminalEquiv_apply, terminalEquiv_apply, extEquiv_map, Sheaf.H.map_apply]
  symm
  apply Ext.comp_assoc
  all_goals omega

lemma equiv₀_terminalEquiv (F : Sheaf J AddCommGrpCat.{v}) {T : C} (hT : IsTerminal T)
    (x : F.H' 0 T) :
    Sheaf.H.equiv₀ F hT (terminalEquiv F 0 hT x) = zeroEquiv F T x := by
  obtain ⟨y, rfl⟩ := (extEquiv F 0 T).symm.surjective x
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  rw [zeroEquiv_mk₀, terminalEquiv_apply, AddEquiv.apply_symm_apply, Ext.mk₀_comp_mk₀]
  obtain ⟨ψ, rfl⟩ : ∃ ψ, (freeSheafIsoConst hT).hom ≫ ψ = φ :=
    ⟨(freeSheafIsoConst hT).inv ≫ φ, by simp⟩
  rw [Iso.inv_hom_id_assoc, freeSheafHomEquiv_comp]
  have h : (Ext.addEquiv₀ (Ext.mk₀.{w} ψ)) = ψ := Ext.addEquiv₀.apply_symm_apply ψ
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, h]
  have h₁ := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality J (freePresheafIsoConst hT).hom) (op T))
    (FreeAbelianGroup.of (𝟙 T))
  exact congrArg (ψ.hom.app (op T)) h₁

instance subsingleton_of_injective (F : Sheaf J AddCommGrpCat.{v}) [Injective F] (n : ℕ) (U : C) :
    Subsingleton (F.H' (n + 1) U) :=
  subsingleton_of_forall_eq 0 fun _ ↦
    (extEquiv F (n + 1) U).injective ((Ext.eq_zero_of_injective _).trans (map_zero _).symm)

lemma subsingleton_of_subsingleton_freeSheaf (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C)
    [Subsingleton (((freeSheaf J).obj U).obj.obj (op U))] : Subsingleton (F.H' n U) := by
  have h : 𝟙 ((freeSheaf J).obj U) = 0 :=
    (freeSheafHomEquiv U _).injective (Subsingleton.elim _ _)
  refine subsingleton_of_forall_eq 0 fun x ↦ (extEquiv F n U).injective ?_
  rw [← Ext.mk₀_id_comp (extEquiv F n U x), h, Ext.mk₀_zero, Ext.zero_comp, map_zero]

end GlobalTheory.SiteCoh
