import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR.SubGrp

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

section Abstract

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

def ptSub {A X : C} [GrpObj A] (h : X ⟶ A) (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1)
    (T : C) : Subgroup (T ⟶ A) where
  carrier := {f | ∃ a : T ⟶ X, a ≫ h = f}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨lift a b ≫ m, ?_⟩
    rw [Category.assoc, hm, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  one_mem' := ⟨toUnit T ≫ e, by rw [Category.assoc, he, MonObj.comp_one]⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a ≫ i, ?_⟩
    rw [eq_inv_iff_mul_eq_one, Category.assoc, ← MonObj.comp_mul, hi, MonObj.comp_one]

def ptFunctor {A X : C} [GrpObj A] (h : X ⟶ A) (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    Cᵒᵖ ⥤ GrpCat.{v} where
  obj T := GrpCat.of (ptSub h m e i hm he hi (unop T))
  map {T T'} f := GrpCat.ofHom
    { toFun := fun x => ⟨f.unop ≫ x.1, by
        obtain ⟨a, ha⟩ := x.2
        exact ⟨f.unop ≫ a, by rw [Category.assoc, ha]⟩⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' := fun x y => Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext (Category.id_comp x.1))
  map_comp f g := GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext (Category.assoc _ _ x.1))

def ptRep {A X : C} [GrpObj A] (h : X ⟶ A) [Mono h] (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    (ptFunctor h m e i hm he hi ⋙ forget _).RepresentableBy X where
  homEquiv {T} := Equiv.ofBijective
    (fun a => (⟨a ≫ h, a, rfl⟩ : ptSub h m e i hm he hi T))
    ⟨fun a b hab => (cancel_mono h).1 (congrArg Subtype.val hab),
      fun x => by
        obtain ⟨a, ha⟩ := x.2
        exact ⟨a, Subtype.ext ha⟩⟩
  homEquiv_comp f g := Subtype.ext (Category.assoc _ _ _)

theorem exists_grpObj_of_mono {A X : C} [GrpObj A] (h : X ⟶ A) [Mono h] (m : X ⊗ X ⟶ X)
    (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    ∃ _ : GrpObj X, IsMonHom h := by
  let α := ptRep h m e i hm he hi
  letI G : GrpObj X := GrpObj.ofRepresentableBy X _ α
  have key : ∀ {T : C} (a b : T ⟶ X), (a * b) ≫ h = (a ≫ h) * (b ≫ h) := fun {T} a b =>
    congrArg Subtype.val
      (((yonedaGrpObjIsoOfRepresentableBy X _ α).hom.app (op T)).hom.map_mul a b)
  have key1 : ∀ {T : C}, (1 : T ⟶ X) ≫ h = 1 := fun {T} =>
    congrArg Subtype.val
      (((yonedaGrpObjIsoOfRepresentableBy X _ α).hom.app (op T)).hom.map_one)
  refine ⟨G, ⟨?_, ?_⟩⟩
  · have := key1 (T := 𝟙_ C)
    simpa [Hom.one_def, toUnit_unique (toUnit (𝟙_ C)) (𝟙 _)] using this
  · have := key (fst X X) (snd X X)
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this, Hom.mul_def]
    congr 1
    ext <;> simp

end Abstract

section Scheme

variable {R : Type} [CommRing R]

theorem exists_eq_spMap {S B : Type} [CommRing S] [Algebra R S] [CommRing B] [Algebra R B]
    (x : sp (R₀ := R) S ⟶ sp (R₀ := R) B) : ∃ g : B →ₐ[R] S, x = spMap g := by
  obtain ⟨g, hg⟩ := Spec.map_surjective x.left
  have h : Spec.map g ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := hg ▸ Over.w x
  rw [← Spec.map_comp] at h
  exact ⟨⟨g.hom, RingHom.congr_fun (congrArg (·.hom) (Spec.map_injective h))⟩,
    Over.OverMorphism.ext hg.symm⟩

theorem exists_sp_iso (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (j : sp (R₀ := R) S ⟶ T), IsIso j := by
  have hU := isAffineOpen_top T.left
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (hU.fromSpec ≫ T.hom)
  letI : Algebra R Γ(T.left, ⊤) := ρ.hom.toAlgebra
  let j : sp (R₀ := R) Γ(T.left, ⊤) ⟶ T := Over.homMk hU.fromSpec hρ.symm
  have : IsIso j.left := by
    change IsIso hU.fromSpec
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  have hj : IsIso ((Over.forget _).map j) := ‹IsIso j.left›
  exact ⟨Γ(T.left, ⊤), inferInstance, inferInstance, j, isIso_of_reflects_iso j (Over.forget _)⟩

variable {A : Over (Spec (CommRingCat.of R))} [GrpObj A] {B : Type} [CommRing B] [Algebra R B]
  {h : sp (R₀ := R) B ⟶ A}

theorem affine_mono (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a b : T ⟶ sp (R₀ := R) B) (hab : a ≫ h = b ≫ h) : a = b := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨φ', hφ'⟩ := exists_eq_spMap (j ≫ b)
  have := H.mono S φ φ' (by rw [← hφ, ← hφ', Category.assoc, Category.assoc, hab])
  rw [← cancel_epi j, hφ, hφ', this]

theorem affine_mul (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a b : T ⟶ sp (R₀ := R) B) : ∃ c : T ⟶ sp (R₀ := R) B, c ≫ h = (a ≫ h) * (b ≫ h) := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨φ', hφ'⟩ := exists_eq_spMap (j ≫ b)
  obtain ⟨χ, hχ⟩ := H.mul S φ φ'
  refine ⟨inv j ≫ spMap χ, ?_⟩
  rw [Category.assoc, hχ, ← hφ, ← hφ', MonObj.comp_mul, Category.assoc, Category.assoc,
    IsIso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc]

theorem affine_one (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] :
    ∃ c : T ⟶ sp (R₀ := R) B, c ≫ h = 1 := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨χ, hχ⟩ := H.one S
  exact ⟨inv j ≫ spMap χ, by rw [Category.assoc, hχ, MonObj.comp_one]⟩

theorem affine_inv (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a : T ⟶ sp (R₀ := R) B) : ∃ c : T ⟶ sp (R₀ := R) B, (c ≫ h) * (a ≫ h) = 1 := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨χ, hχ⟩ := H.inv S φ
  refine ⟨inv j ≫ spMap χ, ?_⟩
  rw [← hφ] at hχ
  have := congrArg (inv j ≫ ·) hχ
  simp only [MonObj.comp_mul, MonObj.comp_one, Category.assoc, IsIso.inv_hom_id_assoc] at this
  simpa [Category.assoc] using this

theorem mono_of_isFinFlatSub (H : IsFinFlatSub A B h) : Mono h := by
  constructor
  intro T a b hab
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext T.left.affineCover _ _ fun i => ?_
  let T' : Over (Spec (CommRingCat.of R)) := Over.mk (T.left.affineCover.f i ≫ T.hom)
  let j : T' ⟶ T := Over.homMk (T.left.affineCover.f i) rfl
  haveI : IsAffine T'.left := inferInstanceAs (IsAffine (T.left.affineCover.X i))
  have := affine_mono H (j ≫ a) (j ≫ b) (by rw [Category.assoc, Category.assoc, hab])
  exact congrArg (·.left) this

theorem grpObj_of_isFinFlatSub (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (B : Type)
    [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A) (H : IsFinFlatSub A B h) :
    ∃ _ : GrpObj (sp (R₀ := R) B), IsMonHom h ∧ Mono h := by
  have hmono := mono_of_isFinFlatSub H
  haveI : IsAffine (sp (R₀ := R) B).left := inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
    inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (sp (R₀ := R) B ⊗ sp (R₀ := R) B).left :=
    inferInstanceAs (IsAffine (pullback (sp (R₀ := R) B).hom (sp (R₀ := R) B).hom))
  obtain ⟨m, hm⟩ := affine_mul H (fst _ _) (snd _ _)
  obtain ⟨e, he⟩ := affine_one H (T := 𝟙_ _)
  obtain ⟨i, hi⟩ := affine_inv H (𝟙 _)
  rw [Category.id_comp] at hi
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono h m e i hm he hi
  exact ⟨G, hG, hmono⟩

end Scheme

end GlobalTheory.CompanionTheory.Ar.GR.SubGrp
