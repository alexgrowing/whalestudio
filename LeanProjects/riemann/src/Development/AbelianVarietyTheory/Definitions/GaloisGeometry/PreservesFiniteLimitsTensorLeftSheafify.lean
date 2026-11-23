import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.YonedaAddNaturalityLeft
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsGrothendieckAbelianPresheaf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory Enriched.FunctorCategory
open scoped MonoidalClosed

namespace GlobalTheory.Et

section Site

variable {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C) (S : Type 1) [CommRing S]

instance (F G : Cᵒᵖ ⥤ ModuleCat.{1} S) : HasFunctorEnrichedHom (ModuleCat.{1} S) F G := inferInstance

instance (F G : Cᵒᵖ ⥤ ModuleCat.{1} S) : HasEnrichedHom (ModuleCat.{1} S) F G := inferInstance

instance : (J.W (A := ModuleCat.{1} S)).IsMonoidal := GrothendieckTopology.W.monoidal

instance : MonoidalClosed (Cᵒᵖ ⥤ ModuleCat.{1} S) := MonoidalClosed.FunctorCategory.monoidalClosed

theorem preservesFiniteLimits_tensorLeft_presheaf (P : Cᵒᵖ ⥤ ModuleCat.{1} S) (hP : ∀ U, Module.Flat S (P.obj U)) :
    PreservesFiniteLimits (tensorLeft P) := by
  constructor
  intro K _ _
  apply preservesLimitsOfShape_of_evaluation
  intro U
  have : Module.Flat S (P.obj U) := hP U
  have e : (evaluation Cᵒᵖ (ModuleCat.{1} S)).obj U ⋙ tensorLeft (P.obj U) ≅
      tensorLeft P ⋙ (evaluation Cᵒᵖ (ModuleCat.{1} S)).obj U := NatIso.ofComponents (fun F => Iso.refl _) (by
        intro F G g
        simp)
  exact preservesLimitsOfShape_of_natIso e

variable [HasSheafify J (ModuleCat.{1} S)]

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

def tensorLeftSheafifyIso (P : Cᵒᵖ ⥤ ModuleCat.{1} S) :
    tensorLeft ((presheafToSheaf J _).obj P) ≅ sheafToPresheaf J _ ⋙ tensorLeft P ⋙ presheafToSheaf J _ :=
  NatIso.ofComponents (fun F => whiskerLeftIso _ (asIso ((sheafificationAdjunction J _).counit.app F)).symm ≪≫
      Functor.Monoidal.μIso (presheafToSheaf J _) P F.obj) (by
    intro F G g
    simp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, asIso_inv, Functor.Monoidal.μIso_hom]
    have h : g ≫ inv ((sheafificationAdjunction J _).counit.app G) =
        inv ((sheafificationAdjunction J _).counit.app F) ≫ (presheafToSheaf J _).map ((sheafToPresheaf J _).map g) := by
      rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
      exact ((sheafificationAdjunction J _).counit.naturality g).symm
    change _ ◁ g ≫ _ = _ ≫ (presheafToSheaf J _).map (P ◁ (sheafToPresheaf J _).map g)
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, h, MonoidalCategory.whiskerLeft_comp_assoc, Category.assoc]
    exact congrArg (_ ≫ ·) (Functor.LaxMonoidal.μ_natural_right (presheafToSheaf J (ModuleCat.{1} S)) P
      ((sheafToPresheaf J _).map g)))

theorem preservesFiniteLimits_tensorLeft_sheafify (P : Cᵒᵖ ⥤ ModuleCat.{1} S) (hP : ∀ U, Module.Flat S (P.obj U)) :
    PreservesFiniteLimits (tensorLeft ((presheafToSheaf J _).obj P)) := by
  have := preservesFiniteLimits_tensorLeft_presheaf S P hP
  exact preservesFiniteLimits_of_natIso (tensorLeftSheafifyIso J S P).symm

end Site

section Lin

variable {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C) (S : Type 1) [CommRing S]

instance tensorLeft_presheaf_additive (P : Cᵒᵖ ⥤ ModuleCat.{1} S) : (tensorLeft P).Additive where
  map_add {F G} f g := by
    ext U : 2
    exact MonoidalPreadditive.whiskerLeft_add ..

instance tensorLeft_presheaf_linear (P : Cᵒᵖ ⥤ ModuleCat.{1} S) : (tensorLeft P).Linear S where
  map_smul {F G} f r := by
    ext U : 2
    exact MonoidalLinear.whiskerLeft_smul ..

variable [HasSheafify J (ModuleCat.{1} S)]

instance presheafToSheaf_linear : (presheafToSheaf J (ModuleCat.{1} S)).Linear S where
  map_smul {P Q} f r := by
    let adj := sheafificationAdjunction J (ModuleCat.{1} S)
    apply (adj.homEquiv P ((presheafToSheaf J _).obj Q)).injective
    rw [adj.homEquiv_unit, adj.homEquiv_unit]
    have h1 := adj.unit.naturality (r • f)
    have h2 := adj.unit.naturality f
    dsimp at h1 h2
    change adj.unit.app P ≫ ((presheafToSheaf J (ModuleCat.{1} S)).map (r • f)).hom =
      adj.unit.app P ≫ (r • ((presheafToSheaf J (ModuleCat.{1} S)).map f).hom)
    rw [Linear.comp_smul, ← h2, ← h1, Linear.smul_comp]

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

theorem tensorLeft_sheaf_additive (F : Sheaf J (ModuleCat.{1} S)) : (tensorLeft F).Additive := by
  have e : tensorLeft F ≅ sheafToPresheaf J _ ⋙ tensorLeft F.obj ⋙ presheafToSheaf J _ :=
    (tensoringLeft _).mapIso (asIso ((sheafificationAdjunction J _).counit.app F)).symm ≪≫
      tensorLeftSheafifyIso J S F.obj
  exact Functor.additive_of_iso e.symm

theorem tensorLeft_sheaf_linear (F : Sheaf J (ModuleCat.{1} S)) :
    letI := tensorLeft_sheaf_additive J S F
    (tensorLeft F).Linear S := by
  letI := tensorLeft_sheaf_additive J S F
  have e : tensorLeft F ≅ sheafToPresheaf J _ ⋙ tensorLeft F.obj ⋙ presheafToSheaf J _ :=
    (tensoringLeft _).mapIso (asIso ((sheafificationAdjunction J _).counit.app F)).symm ≪≫
      tensorLeftSheafifyIso J S F.obj
  exact Functor.linear_of_iso S e.symm

end Lin

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

instance : MonoidalCategory (Shv R) := Sheaf.monoidalCategory _ _

instance : SymmetricCategory (Shv R) := Sheaf.symmetricCategory _ _

instance : MonoidalClosed (Shv R) := Monoidal.Reflective.monoidalClosed (sheafificationAdjunction _ _)

instance (F : Shv R) : (tensorLeft F).Additive := tensorLeft_sheaf_additive _ _ F

instance (F : Shv R) : (tensorLeft F).Linear (ULift.{1} R) := tensorLeft_sheaf_linear _ _ F

instance (F : Shv R) : (tensorRight F).Additive :=
  Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight F)

instance (F : Shv R) : (tensorRight F).Linear (ULift.{1} R) :=
  Functor.linear_of_iso _ (BraidedCategory.tensorLeftIsoTensorRight F)

instance (F : Shv R) : PreservesFiniteColimits (tensorRight F) :=
  preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)

abbrev freePre (X : Scheme.{0}) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) :=
  uliftYoneda.{1}.obj X ⋙ ModuleCat.free (ULift.{1} R)

example (X : Scheme.{0}) : (freeOn R).obj X = (presheafToSheaf _ _).obj (freePre R X) := rfl

instance (X : Scheme.{0}) : PreservesFiniteLimits (tensorLeft ((freeOn R).obj X)) :=
  preservesFiniteLimits_tensorLeft_sheafify _ _ (freePre R X) (fun U =>
    inferInstanceAs (Module.Flat (ULift.{1} R) (ULift.{1} (U.unop ⟶ X) →₀ ULift.{1} R)))

class FlatCoef : Prop where
  preservesFiniteLimits_tensorRight : PreservesFiniteLimits (tensorRight (coef R))

attribute [instance] FlatCoef.preservesFiniteLimits_tensorRight

theorem FlatCoef.of_flat (h : ∀ U : Scheme.{0}, Module.Flat R C(U, R)) : FlatCoef R := by
  have : PreservesFiniteLimits (tensorLeft (coef R)) :=
    preservesFiniteLimits_tensorLeft_sheafify _ _ (coefPre R) (fun U => by
      have := h U.unop
      change Module.Flat (ULift.{1} R) (ULift.{1} C(U.unop, R))
      rw [Module.Flat.ulift_left_iff]
      infer_instance)
  exact ⟨preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (coef R))⟩

instance [IsDomain R] [IsBezout R] : FlatCoef R := by
  refine FlatCoef.of_flat R fun U => ?_
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro f hf
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff f).1 hf
  ext u
  have hu := congrArg (fun g : C(U, R) => g u) ha
  simp only [Submonoid.smul_def, ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.zero_apply] at hu
  exact (mul_eq_zero.1 hu).resolve_left (nonZeroDivisors.ne_zero a.2)

example : FlatCoef ℚ := inferInstance
example (p : ℕ) [Fact p.Prime] : FlatCoef ℤ_[p] := inferInstance
example (p : ℕ) [Fact p.Prime] : FlatCoef ℚ_[p] := inferInstance

def coefMulPre : coefPre R ⊗ coefPre R ⟶ coefPre R where
  app U := ModuleCat.ofHom (TensorProduct.lift (LinearMap.mk₂ (ULift.{1} R)
    (fun f g : ULift.{1} C(U.unop, R) => (⟨f.down * g.down⟩ : ULift.{1} C(U.unop, R)))
    (fun _ _ _ => ULift.ext _ _ (add_mul _ _ _))
    (fun c _ _ => ULift.ext _ _ (smul_mul_assoc c.down _ _))
    (fun _ _ _ => ULift.ext _ _ (mul_add _ _ _))
    (fun c _ _ => ULift.ext _ _ (mul_smul_comm c.down _ _))))
  naturality U V f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    rfl

def coefOnePre : 𝟙_ (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ⟶ coefPre R where
  app U := ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ (⟨1⟩ : ULift.{1} C(U.unop, R)))
  naturality U V f := by
    ext c
    exact ULift.ext _ _ (ContinuousMap.ext fun x => rfl)

def freeDiagPre (X : Scheme.{0}) : freePre R X ⟶ freePre R X ⊗ freePre R X where
  app U := ModuleCat.ofHom (Finsupp.linearCombination (ULift.{1} R)
    (fun f => ((Finsupp.single f (1 : ULift.{1} R) : (freePre R X).obj U) ⊗ₜ[ULift.{1} R]
      (Finsupp.single f (1 : ULift.{1} R) : (freePre R X).obj U))))
  naturality U V g := by
    apply ModuleCat.hom_ext
    refine Finsupp.lhom_ext (fun f c => ?_)
    change Finsupp.linearCombination _ _ (Finsupp.mapDomain _ (Finsupp.single f c)) =
      ((freePre R X ⊗ freePre R X).map g).hom (Finsupp.linearCombination _ _ (Finsupp.single f c))
    rw [Finsupp.mapDomain_single]
    erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul]
    congr 1
    exact (congrArg₂ (fun (a b : (freePre R X).obj V) => a ⊗ₜ[ULift.{1} R] b) Finsupp.mapDomain_single Finsupp.mapDomain_single).symm

def freeAugPre (X : Scheme.{0}) : freePre R X ⟶ 𝟙_ (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) where
  app U := ModuleCat.ofHom (Finsupp.linearCombination (ULift.{1} R) (fun _ => (1 : ULift.{1} R)))
  naturality U V g := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro f
    apply LinearMap.ext_ring
    change Finsupp.linearCombination _ _ (Finsupp.mapDomain _ (Finsupp.single f 1)) =
      Finsupp.linearCombination (ULift.{1} R) (fun _ => (1 : ULift.{1} R)) (Finsupp.single f 1)
    simp [Finsupp.mapDomain_single]

def coefMul : coef R ⊗ coef R ⟶ coef R :=
  Functor.LaxMonoidal.μ (presheafToSheaf _ _) (coefPre R) (coefPre R) ≫ (presheafToSheaf _ _).map (coefMulPre R)

def coefOne : 𝟙_ (Shv R) ⟶ coef R :=
  Functor.LaxMonoidal.ε (presheafToSheaf _ _) ≫ (presheafToSheaf _ _).map (coefOnePre R)

def freeDiag (X : Scheme.{0}) : (freeOn R).obj X ⟶ (freeOn R).obj X ⊗ (freeOn R).obj X :=
  (presheafToSheaf _ _).map (freeDiagPre R X) ≫ Functor.OplaxMonoidal.δ (presheafToSheaf _ _) _ _

def freeAug (X : Scheme.{0}) : (freeOn R).obj X ⟶ 𝟙_ (Shv R) :=
  (presheafToSheaf _ _).map (freeAugPre R X) ≫ Functor.OplaxMonoidal.η (presheafToSheaf _ _)

section Cup

variable [FlatCoef R]

def cupExt (X : Scheme.{0}) {i j n : ℕ} (h : i + j = n) (a : HS R (coef R) i X) (b : HS R (coef R) j X) :
    HS R (coef R) n X :=
  (Abelian.Ext.mk₀ (freeDiag R X)).comp ((b.mapExactFunctor (tensorLeft ((freeOn R).obj X))).comp
    ((a.mapExactFunctor (tensorRight (coef R))).comp (Abelian.Ext.mk₀ (coefMul R)) (add_zero i))
    (show j + i = n by omega)) (zero_add n)

theorem cupExt_add_left (X : Scheme.{0}) {i j n : ℕ} (h : i + j = n) (a a' : HS R (coef R) i X)
    (b : HS R (coef R) j X) : cupExt R X h (a + a') b = cupExt R X h a b + cupExt R X h a' b := by
  simp only [cupExt, Abelian.Ext.mapExactFunctor_add, Abelian.Ext.add_comp, Abelian.Ext.comp_add]

theorem cupExt_add_right (X : Scheme.{0}) {i j n : ℕ} (h : i + j = n) (a : HS R (coef R) i X)
    (b b' : HS R (coef R) j X) : cupExt R X h a (b + b') = cupExt R X h a b + cupExt R X h a b' := by
  simp only [cupExt, Abelian.Ext.mapExactFunctor_add, Abelian.Ext.add_comp, Abelian.Ext.comp_add]

theorem cupExt_smul_left (X : Scheme.{0}) {i j n : ℕ} (h : i + j = n) (r : ULift.{1} R) (a : HS R (coef R) i X)
    (b : HS R (coef R) j X) : cupExt R X h (r • a) b = r • cupExt R X h a b := by
  simp only [cupExt, Functor.mapExactFunctor_smul, Abelian.Ext.smul_comp, Abelian.Ext.comp_smul]

theorem cupExt_smul_right (X : Scheme.{0}) {i j n : ℕ} (h : i + j = n) (r : ULift.{1} R) (a : HS R (coef R) i X)
    (b : HS R (coef R) j X) : cupExt R X h a (r • b) = r • cupExt R X h a b := by
  simp only [cupExt, Functor.mapExactFunctor_smul, Abelian.Ext.smul_comp, Abelian.Ext.comp_smul]

def cupN (X : Scheme.{0}) (i j n : ℕ) (h : i + j = n) : H R i X →ₗ[R] H R j X →ₗ[R] H R n X :=
  LinearMap.mk₂ R (fun a b => cupExt R X h a b)
    (fun a a' b => cupExt_add_left R X h a a' b)
    (fun r a b => cupExt_smul_left R X h (ULift.up r) a b)
    (fun a b b' => cupExt_add_right R X h a b b')
    (fun r a b => cupExt_smul_right R X h (ULift.up r) a b)

def cup (X : Scheme.{0}) (i j : ℕ) : H R i X →ₗ[R] H R j X →ₗ[R] H R (i + j) X := cupN R X i j (i + j) rfl

theorem cupN_apply (X : Scheme.{0}) (i j n : ℕ) (h : i + j = n) (a : H R i X) (b : H R j X) :
    cupN R X i j n h a b = cupExt R X h a b := rfl

theorem cup_eq_cupN (X : Scheme.{0}) (i j : ℕ) : cup R X i j = cupN R X i j (i + j) rfl := rfl

end Cup

section Natural

variable [FlatCoef R]

theorem freeDiagPre_naturality {X Y : Scheme.{0}} (f : X ⟶ Y) :
    ((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} R))).map (uliftYoneda.{1}.map f) ≫ freeDiagPre R Y =
      freeDiagPre R X ≫ (((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} R))).map (uliftYoneda.{1}.map f) ⊗ₘ
        ((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} R))).map (uliftYoneda.{1}.map f)) := by
  ext U : 2
  apply ModuleCat.hom_ext
  refine Finsupp.lhom_ext (fun g c => ?_)
  change Finsupp.linearCombination _ _ (Finsupp.mapDomain _ (Finsupp.single g c)) =
    ((Functor.whiskerRight (uliftYoneda.{1}.map f) (ModuleCat.free (ULift.{1} R)) ⊗ₘ
        Functor.whiskerRight (uliftYoneda.{1}.map f) (ModuleCat.free (ULift.{1} R))).app U).hom
      (Finsupp.linearCombination _ _ (Finsupp.single g c))
  rw [Finsupp.mapDomain_single]
  erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul]
  congr 1
  exact (congrArg₂ (fun (a b : (freePre R Y).obj U) => a ⊗ₜ[ULift.{1} R] b) Finsupp.mapDomain_single
    Finsupp.mapDomain_single).symm

theorem freeDiag_naturality {X Y : Scheme.{0}} (f : X ⟶ Y) :
    (freeOn R).map f ≫ freeDiag R Y = freeDiag R X ≫ ((freeOn R).map f ⊗ₘ (freeOn R).map f) := by
  change (presheafToSheaf _ _).map _ ≫ (presheafToSheaf _ _).map (freeDiagPre R Y) ≫ _ =
    ((presheafToSheaf _ _).map (freeDiagPre R X) ≫ _) ≫ ((presheafToSheaf _ _).map _ ⊗ₘ (presheafToSheaf _ _).map _)
  rw [Category.assoc, Functor.OplaxMonoidal.δ_natural, ← Functor.map_comp_assoc, freeDiagPre_naturality,
    Functor.map_comp_assoc]

theorem mk₀_comp_cupExt {X Y : Scheme.{0}} (f : X ⟶ Y) {i j n : ℕ} (h : i + j = n) (a : HS R (coef R) i Y)
    (b : HS R (coef R) j Y) :
    (Abelian.Ext.mk₀ ((freeOn R).map f)).comp (cupExt R Y h a b) (zero_add n) =
      cupExt R X h ((Abelian.Ext.mk₀ ((freeOn R).map f)).comp a (zero_add i))
        ((Abelian.Ext.mk₀ ((freeOn R).map f)).comp b (zero_add j)) := by
  simp only [cupExt]
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀_assoc, freeDiag_naturality,
    ← Abelian.Ext.mk₀_comp_mk₀_assoc]
  congr 1
  rw [Abelian.Ext.comp_assoc _ _ _ (zero_add j) (show j + i = n by omega) (by omega),
    Abelian.Ext.comp_assoc_of_third_deg_zero, ← Abelian.Ext.comp_assoc_of_second_deg_zero]
  have hτ := GlobalTheory.ChangeRing.mapExactFunctor_natTrans.{1, 1} (tensorLeft ((freeOn R).obj X))
    (tensorLeft ((freeOn R).obj Y)) ((tensoringLeft (Shv R)).map ((freeOn R).map f)) j b
  erw [hτ]
  rw [Abelian.Ext.comp_assoc _ _ _ (zero_add j) (show j + i = n by omega) (by omega), Abelian.Ext.mk₀_comp_mk₀_assoc]
  congr 2
  exact MonoidalCategory.tensorHom_def' (C := Shv R) ((freeOn R).map f) ((freeOn R).map f)

theorem pull_cupN {X Y : Scheme.{0}} (f : X ⟶ Y) (i j n : ℕ) (h : i + j = n) (a : H R i Y) (b : H R j Y) :
    pull R n f (cupN R Y i j n h a b) = cupN R X i j n h (pull R i f a) (pull R j f b) :=
  mk₀_comp_cupExt R f h a b

theorem pull_cup {X Y : Scheme.{0}} (f : X ⟶ Y) (i j : ℕ) (a : H R i Y) (b : H R j Y) :
    pull R (i + j) f (cup R Y i j a b) = cup R X i j (pull R i f a) (pull R j f b) :=
  pull_cupN R f i j (i + j) rfl a b

end Natural

section DegreeZero

variable [FlatCoef R]

def ofPre {X : Scheme.{0}} (γ : freePre R X ⟶ coefPre R) : H R 0 X := Abelian.Ext.mk₀ ((presheafToSheaf _ _).map γ)

theorem cupExt_mk₀ (X : Scheme.{0}) (g g' : (freeOn R).obj X ⟶ coef R) :
    cupExt R X (rfl : 0 + 0 = 0) (Abelian.Ext.mk₀ g) (Abelian.Ext.mk₀ g') =
      Abelian.Ext.mk₀ (freeDiag R X ≫ (g ⊗ₘ g') ≫ coefMul R) := by
  simp only [cupExt, Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
  congr 1
  rw [MonoidalCategory.tensorHom_def' (C := Shv R) g g', Category.assoc]
  rfl

theorem cupN_ofPre (X : Scheme.{0}) (γ γ' : freePre R X ⟶ coefPre R) :
    cupN R X 0 0 0 rfl (ofPre R γ) (ofPre R γ') = ofPre R (freeDiagPre R X ≫ (γ ⊗ₘ γ') ≫ coefMulPre R) := by
  refine (cupExt_mk₀ R X _ _).trans (congrArg Abelian.Ext.mk₀ ?_)
  simp only [freeDiag, coefMul, Functor.map_comp]
  erw [Category.assoc, Functor.OplaxMonoidal.δ_natural_assoc, Functor.Monoidal.δ_μ_assoc]
  rfl

theorem e_ofPre (X : Scheme.{0}) (γ : freePre R X ⟶ coefPre R) :
    H0.e R X (ofPre R γ) = (γ.app (op X) (Finsupp.single (ULift.up (𝟙 X)) 1)).down := by
  have h1 : (sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _
      ((presheafToSheaf _ _).map γ) = γ ≫ toSheafify _ (coefPre R) := by
    rw [Adjunction.homEquiv_unit]
    exact ((sheafificationAdjunction _ _).unit.naturality γ).symm
  have h0 : Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (ofPre R γ) = (presheafToSheaf _ _).map γ :=
    Abelian.Ext.addEquiv₀.apply_symm_apply _
  have key : H0.e R X (ofPre R γ) = AddEquiv.ulift ((((isoSheafify _ (H0.sh R)).app (op X)).symm.toLinearEquiv)
      (H0.yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (ofPre R γ))))) := rfl
  rw [key, h0]
  erw [h1]
  have h3 := ConcreteCategory.congr_hom ((isoSheafify _ (H0.sh R)).hom_inv_id_app (op X))
    (γ.app (op X) (Finsupp.single (ULift.up (𝟙 X)) 1))
  rw [isoSheafify_hom] at h3
  exact congrArg ULift.down h3

theorem homEquiv_map_ofPre {X : Scheme.{0}} (γ : freePre R X ⟶ coefPre R) :
    (sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _
      ((presheafToSheaf _ _).map γ) = γ ≫ toSheafify _ (coefPre R) := by
  rw [Adjunction.homEquiv_unit]
  exact ((sheafificationAdjunction _ _).unit.naturality γ).symm

theorem exists_ofPre {X : Scheme.{0}} (x : H R 0 X) : ∃ γ : freePre R X ⟶ coefPre R, ofPre R γ = x := by
  obtain ⟨g, rfl⟩ := (Abelian.Ext.mk₀_bijective ((freeOn R).obj X) (coef R)).surjective x
  let adj := sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  refine ⟨adj.homEquiv _ _ g ≫ (isoSheafify _ (H0.sh R)).inv, ?_⟩
  refine congrArg Abelian.Ext.mk₀ ((adj.homEquiv _ _).injective ?_)
  erw [homEquiv_map_ofPre]
  have hi : (isoSheafify _ (H0.sh R)).inv ≫ toSheafify Scheme.proetaleTopology.{0} (coefPre R) = 𝟙 _ := by
    rw [← isoSheafify_hom _ (H0.sh R)]
    exact Iso.inv_hom_id _
  exact (Category.assoc _ _ _).trans ((congrArg (adj.homEquiv _ _ g ≫ ·) hi).trans (Category.comp_id _))

theorem e_cupN (X : Scheme.{0}) (x y : H R 0 X) :
    H0.e R X (cupN R X 0 0 0 rfl x y) = H0.e R X x * H0.e R X y := by
  obtain ⟨γ, rfl⟩ := exists_ofPre R x
  obtain ⟨γ', rfl⟩ := exists_ofPre R y
  rw [cupN_ofPre, e_ofPre, e_ofPre, e_ofPre]
  change ((coefMulPre R).app (op X) (((γ ⊗ₘ γ').app (op X)) ((freeDiagPre R X).app (op X)
    (Finsupp.single (ULift.up (𝟙 X)) 1)))).down = _
  erw [Finsupp.linearCombination_single, one_smul]
  rfl

theorem e_cup (X : Scheme.{0}) (x y : H R 0 X) : H0.e R X (cup R X 0 0 x y) = H0.e R X x * H0.e R X y :=
  e_cupN R X x y

end DegreeZero

section One

variable [FlatCoef R]

def one (X : Scheme.{0}) : H R 0 X := Abelian.Ext.mk₀ (freeAug R X ≫ coefOne R)

theorem one_eq_ofPre (X : Scheme.{0}) : one R X = ofPre R (freeAugPre R X ≫ coefOnePre R) := by
  refine congrArg Abelian.Ext.mk₀ ?_
  simp only [freeAug, coefOne, Functor.map_comp]
  erw [Category.assoc, Functor.Monoidal.η_ε_assoc]

theorem e_one (X : Scheme.{0}) : H0.e R X (one R X) = 1 := by
  rw [one_eq_ofPre, e_ofPre]
  change ((coefOnePre R).app (op X) ((freeAugPre R X).app (op X) (Finsupp.single (ULift.up (𝟙 X)) 1))).down = 1
  erw [Finsupp.linearCombination_single]
  ext x
  change ((((1 : ULift.{1} R) • (1 : ULift.{1} R)) • (⟨1⟩ : ULift.{1} C(X, R))).down) x = (1 : C(X, R)) x
  simp

theorem gal_cup {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) (i j : ℕ) (σ : Ω ≃ₐ[k] Ω) (a : H R i (geom Ω p)) (b : H R j (geom Ω p)) :
    gal R Ω p (i + j) σ (cup R (geom Ω p) i j a b) = cup R (geom Ω p) i j (gal R Ω p i σ a) (gal R Ω p j σ b) :=
  pull_cup R _ i j a b

end One

section Examples

variable (X : Scheme.{0})

example (p : ℕ) [Fact p.Prime] : cup ℚ_[p] X 0 0 (one ℚ_[p] X) (one ℚ_[p] X) = (H0.e ℚ_[p] X).symm 1 := by
  apply (H0.e ℚ_[p] X).injective
  rw [e_cup, e_one, LinearEquiv.apply_symm_apply, one_mul]

example (p : ℕ) [Fact p.Prime] [Nonempty X] : one ℤ_[p] X ≠ 0 := by
  intro h
  have h1 := e_one ℤ_[p] X
  rw [h, map_zero] at h1
  exact zero_ne_one (DFunLike.congr_fun h1 (Classical.arbitrary X))

example (p : ℕ) [Fact p.Prime] (f g : C(X, ℤ_[p])) :
    H0.e ℤ_[p] X (cup ℤ_[p] X 0 0 ((H0.e ℤ_[p] X).symm f) ((H0.e ℤ_[p] X).symm g)) = f * g := by
  rw [e_cup, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end Examples

end GlobalTheory.Et
