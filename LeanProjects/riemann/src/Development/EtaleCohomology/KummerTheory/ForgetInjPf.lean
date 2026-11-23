import Development.EtaleCohomology.KummerTheory.InjSlicePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ForgetInjPf

universe w v u

variable {C : Type u} [Category.{v} C] {U : C} {A : Type w} [Category.{max u v} A]
  [HasCoproducts.{v} A]

abbrev zObj (P : (Over U)ᵒᵖ ⥤ A) (X : C) : A := ∐ (fun s : X ⟶ U => P.obj (op (Over.mk s)))

lemma zι_eq (P : (Over U)ᵒᵖ ⥤ A) {Y : C} {V : Over U} {t t' : Y ⟶ U} (h : t = t')
    (a : Over.mk t ⟶ V) (a' : Over.mk t' ⟶ V) (ha : a.left = a'.left) :
    P.map a.op ≫ Sigma.ι (fun s : Y ⟶ U => P.obj (op (Over.mk s))) t =
      P.map a'.op ≫ Sigma.ι (fun s : Y ⟶ U => P.obj (op (Over.mk s))) t' := by
  subst h
  have : a = a' := Over.OverMorphism.ext ha
  rw [this]

def zMap (P : (Over U)ᵒᵖ ⥤ A) {X Y : C} (g : Y ⟶ X) : zObj P X ⟶ zObj P Y :=
  Sigma.desc fun s => P.map (Over.homMk g rfl : Over.mk (g ≫ s) ⟶ Over.mk s).op ≫
    Sigma.ι (fun s : Y ⟶ U => P.obj (op (Over.mk s))) (g ≫ s)

@[reassoc (attr := simp)]
lemma ι_zMap (P : (Over U)ᵒᵖ ⥤ A) {X Y : C} (g : Y ⟶ X) (s : X ⟶ U) :
    Sigma.ι (fun s : X ⟶ U => P.obj (op (Over.mk s))) s ≫ zMap P g =
      P.map (Over.homMk g rfl : Over.mk (g ≫ s) ⟶ Over.mk s).op ≫
        Sigma.ι (fun s : Y ⟶ U => P.obj (op (Over.mk s))) (g ≫ s) := by
  simp [zMap]

lemma zMap_id (P : (Over U)ᵒᵖ ⥤ A) (X : C) : zMap P (𝟙 X) = 𝟙 _ := by
  apply Sigma.hom_ext; intro s
  rw [ι_zMap, Category.comp_id]
  rw [zι_eq P (Category.id_comp s) (Over.homMk (𝟙 X) rfl : Over.mk (𝟙 _ ≫ s) ⟶ Over.mk s)
      (𝟙 (Over.mk s)) (by simp)]
  simp

lemma zMap_comp (P : (Over U)ᵒᵖ ⥤ A) {X Y Z : C} (f : Z ⟶ Y) (g : Y ⟶ X) :
    zMap P (f ≫ g) = zMap P g ≫ zMap P f := by
  apply Sigma.hom_ext; intro s
  rw [ι_zMap, ι_zMap_assoc, ι_zMap, ← P.map_comp_assoc, ← op_comp]
  exact zι_eq P (Category.assoc _ _ _) _ _ (by simp)

def zPre (P : (Over U)ᵒᵖ ⥤ A) : Cᵒᵖ ⥤ A where
  obj X := zObj P X.unop
  map g := zMap P g.unop
  map_id X := zMap_id P X.unop
  map_comp f g := zMap_comp P g.unop f.unop

def zNatApp {P Q : (Over U)ᵒᵖ ⥤ A} (φ : P ⟶ Q) (X : C) : zObj P X ⟶ zObj Q X :=
  Sigma.desc fun s => φ.app (op (Over.mk s)) ≫ Sigma.ι (fun s : X ⟶ U => Q.obj (op (Over.mk s))) s

@[reassoc (attr := simp)]
lemma ι_zNatApp {P Q : (Over U)ᵒᵖ ⥤ A} (φ : P ⟶ Q) (X : C) (s : X ⟶ U) :
    Sigma.ι (fun s : X ⟶ U => P.obj (op (Over.mk s))) s ≫ zNatApp φ X =
      φ.app (op (Over.mk s)) ≫ Sigma.ι (fun s : X ⟶ U => Q.obj (op (Over.mk s))) s := by
  simp [zNatApp]

def zNat {P Q : (Over U)ᵒᵖ ⥤ A} (φ : P ⟶ Q) : zPre P ⟶ zPre Q where
  app X := zNatApp φ X.unop
  naturality X Y g := by
    show zMap P g.unop ≫ zNatApp φ _ = zNatApp φ _ ≫ zMap Q g.unop
    apply Sigma.hom_ext; intro s
    rw [ι_zMap_assoc, ι_zNatApp, ι_zNatApp_assoc, ι_zMap, ← φ.naturality_assoc]
    all_goals rfl

def zFun : ((Over U)ᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A) where
  obj := zPre
  map := zNat
  map_id P := by
    ext X
    show zNatApp (𝟙 P) X.unop = 𝟙 _
    apply Sigma.hom_ext; intro s
    rw [ι_zNatApp]; simp
  map_comp φ ψ := by
    ext X
    show zNatApp (φ ≫ ψ) X.unop = zNatApp φ X.unop ≫ zNatApp ψ X.unop
    apply Sigma.hom_ext; intro s
    rw [ι_zNatApp, ι_zNatApp_assoc, ι_zNatApp]; simp

def zCoApp (Q : Cᵒᵖ ⥤ A) (X : C) : zObj ((Over.forget U).op ⋙ Q) X ⟶ Q.obj (op X) :=
  Sigma.desc fun _ => 𝟙 (Q.obj (op X))

@[reassoc (attr := simp)]
lemma ι_zCoApp (Q : Cᵒᵖ ⥤ A) (X : C) (s : X ⟶ U) :
    Sigma.ι (fun s : X ⟶ U => ((Over.forget U).op ⋙ Q).obj (op (Over.mk s))) s ≫ zCoApp Q X = 𝟙 _ := by
  unfold zCoApp; erw [colimit.ι_desc]; rfl

def zUnit (P : (Over U)ᵒᵖ ⥤ A) : P ⟶ (Over.forget U).op ⋙ zPre P where
  app V := Sigma.ι (fun s : V.unop.left ⟶ U => P.obj (op (Over.mk s))) V.unop.hom
  naturality V W f := by
    change _ = _ ≫ zMap P f.unop.left
    rw [ι_zMap]
    exact (zι_eq P (Over.w f.unop) (Over.homMk f.unop.left rfl : Over.mk (f.unop.left ≫ V.unop.hom) ⟶ Over.mk V.unop.hom)
      f.unop rfl).symm

def zCounit (Q : Cᵒᵖ ⥤ A) : zPre ((Over.forget U).op ⋙ Q) ⟶ Q where
  app X := zCoApp Q X.unop
  naturality X Y g := by
    show zMap _ g.unop ≫ zCoApp Q _ = zCoApp Q _ ≫ Q.map g
    apply Sigma.hom_ext; intro s
    rw [ι_zMap_assoc]
    erw [ι_zCoApp, ι_zCoApp_assoc]
    simp
    all_goals rfl

def zAdj : (zFun : ((Over U)ᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)) ⊣ (Functor.whiskeringLeft _ _ A).obj (Over.forget U).op :=
  Adjunction.mkOfUnitCounit
    { unit := { app P := zUnit P
                naturality P Q φ := by
                  ext V
                  change φ.app V ≫ Sigma.ι (fun s : V.unop.left ⟶ U => Q.obj (op (Over.mk s))) V.unop.hom =
                    Sigma.ι (fun s : V.unop.left ⟶ U => P.obj (op (Over.mk s))) V.unop.hom ≫ zNatApp φ V.unop.left
                  rw [ι_zNatApp]; all_goals rfl }
      counit := { app Q := zCounit Q
                  naturality P Q φ := by
                    ext X
                    show zNatApp _ X.unop ≫ zCoApp Q X.unop = zCoApp P X.unop ≫ φ.app X
                    apply Sigma.hom_ext; intro s
                    erw [ι_zNatApp_assoc, ι_zCoApp, ι_zCoApp_assoc]
                    simp
                    all_goals rfl }
      left_triangle := by
        ext P X
        simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
          NatTrans.id_app, Category.id_comp]
        erw [Category.id_comp]
        show zNatApp (zUnit P) X.unop ≫ zCoApp (zPre P) X.unop = 𝟙 _
        apply Sigma.hom_ext; intro s
        rw [ι_zNatApp_assoc]; erw [ι_zCoApp]; simp
        all_goals rfl
      right_triangle := by
        ext Q V
        simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
          NatTrans.id_app, Category.id_comp]
        try erw [Category.id_comp]
        change Sigma.ι (fun s : V.unop.left ⟶ U => ((Over.forget U).op ⋙ Q).obj (op (Over.mk s))) V.unop.hom ≫
          zCoApp Q V.unop.left = 𝟙 _
        erw [ι_zCoApp]; all_goals rfl }

lemma zNatApp_eq_map {P Q : (Over U)ᵒᵖ ⥤ A} (φ : P ⟶ Q) (X : C) :
    zNatApp φ X = Limits.Sigma.map fun s : X ⟶ U => φ.app (op (Over.mk s)) := by
  apply Sigma.hom_ext; intro s; rw [ι_zNatApp]; simp

lemma sigmaMap_mono [HasFiniteLimits A] {T : Type v} [HasExactColimitsOfShape (Discrete T) A] {f g : T → A}
    (p : ∀ j, f j ⟶ g j) [∀ j, Mono (p j)] : Mono (Limits.Sigma.map p) := by
  let q : Discrete.functor f ⟶ Discrete.functor g := Discrete.natTrans (fun j => p j.as)
  have : ∀ j, Mono (q.app j) := fun j => (inferInstance : Mono (p j.as))
  have : Mono q := NatTrans.mono_of_mono_app _
  have := preservesMonomorphisms_of_preservesLimitsOfShape (colim : (Discrete T ⥤ A) ⥤ A)
  exact (colim : (Discrete T ⥤ A) ⥤ A).map_mono q

instance [HasFiniteLimits A] [∀ T : Type v, HasExactColimitsOfShape (Discrete T) A] : (zFun : ((Over U)ᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)).PreservesMonomorphisms where
  preserves {P Q} φ _ := by
    rw [NatTrans.mono_iff_mono_app]
    intro X
    change Mono (zNatApp φ X.unop)
    rw [zNatApp_eq_map]
    have : ∀ V, Mono (φ.app V) := fun V => (NatTrans.mono_iff_mono_app φ).1 inferInstance V
    exact sigmaMap_mono _

section Sheaf

variable (J : GrothendieckTopology C) [HasSheafify J A]

def sheafZ (U : C) : Sheaf (J.over U) A ⥤ Sheaf J A :=
  sheafToPresheaf _ _ ⋙ zFun ⋙ presheafToSheaf J A

def sheafZAdj (U : C) : sheafZ J U ⊣ J.overPullback A U :=
  ((zAdj (U := U)).comp (sheafificationAdjunction J A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

instance [HasFiniteLimits A] [∀ T : Type v, HasExactColimitsOfShape (Discrete T) A] (U : C) :
    (sheafZ (A := A) J U).PreservesMonomorphisms := by
  unfold sheafZ; infer_instance

end Sheaf

end LateralTheory.KummerTheory.ForgetInjPf

namespace LateralTheory.KummerTheory

open LateralTheory.KummerTheory.ForgetInjPf in
theorem ForgetInj_of : ForgetInj := by
  intro R _ F _ S
  refine ⟨((Scheme.etaleTopology.overPullback (ModuleCat.{1} (ULift.{1} R)) S).obj F).2, ?_⟩
  have := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafZAdj (A := ModuleCat.{1} (ULift.{1} R)) Scheme.etaleTopology S)
  exact inferInstanceAs (Injective ((Scheme.etaleTopology.overPullback (ModuleCat.{1} (ULift.{1} R)) S).obj F))

end LateralTheory.KummerTheory
