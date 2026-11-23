import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TPullTMap
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.CH UpperTheory.Ru.crystallineComparison UpperTheory.Ru.crystallineComparison.Th

namespace UpperTheory.CmpR

variable {C : Type 1} [Category.{0} C] {R : Type} [CommRing R]

private noncomputable def ulF (F : C ⥤ ModuleCat.{0} R) : Coef C where
  obj A := AddCommGrpCat.of (ULift.{1} (F.obj A))
  map φ := AddCommGrpCat.ofHom
    (AddEquiv.ulift.symm.toAddMonoidHom.comp
      ((F.map φ).hom.toAddMonoidHom.comp AddEquiv.ulift.toAddMonoidHom))
  map_id A := by
    ext x
    simp [AddEquiv.ulift]
  map_comp φ ψ := by
    ext x
    simp [AddEquiv.ulift]

private noncomputable def cmp (P : C ⥤ Type) (F : C ⥤ ModuleCat.{0} R) :
    Mor (elF P (zm (ulF F))) (CategoryOfElements.π P ⋙ F) (Int.castRingHom R) where
  G := 𝟭 _
  τ T :=
    { toFun := fun x => ULift.down x
      map_add' := fun _ _ => rfl
      map_smul' := fun n x => by
        change ULift.down (n • (x : ULift.{1} (F.obj T.1))) = (n : R) • ULift.down x
        rw [ULift.smul_down, Int.cast_smul_eq_zsmul] }
  nat _ _ := rfl

private theorem cmp_bij (P : C ⥤ Type) (F : C ⥤ ModuleCat.{0} R) (n : ℕ) :
    Function.Bijective ((cmp P F).hom.f n) := by
  constructor
  · intro a b hab
    funext s
    exact ULift.down_injective (congrFun hab s)
  · intro b
    exact ⟨fun s => ULift.up (b s), rfl⟩

private theorem cmpH_bij (P : C ⥤ Type) (F : C ⥤ ModuleCat.{0} R) (j : ℕ) :
    Function.Bijective ((cmp P F).hom.mapH j) :=
  CrystallineSemistableComparison.P.mapH_bij _ (cmp_bij P F) j

private noncomputable def cmpE (P : C ⥤ Type) (F : C ⥤ ModuleCat.{0} R) (j : ℕ) :
    TH P (ulF F) j ≃+ CH.H (CategoryOfElements.π P ⋙ F) j :=
  AddEquiv.ofBijective ((cmp P F).hom.mapH j).toAddMonoidHom (cmpH_bij P F j)

private theorem cmp_pull {Q P : C ⥤ Type} (u : Q ⟶ P) (F : C ⥤ ModuleCat.{0} R) (j : ℕ)
    (y : TH P (ulF F) j) :
    (elMor u F).pull j ((cmp P F).hom.mapH j y) = (cmp Q F).hom.mapH j (tPull u (ulF F) j y) := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx (elF P (zm (ulF F)))) j).1 y
  rfl

end UpperTheory.CmpR

open UpperTheory.CmpR in
theorem UpperTheory.exists_coefficient_equiv_cohomology_of_elements :
    ∀ (C : Type 1) [Category.{0} C] (R : Type) [CommRing R] (F : C ⥤ ModuleCat.{0} R),
        ∃ (F' : Coef C) (c : ∀ A, F.obj A ≃+ F'.obj A) (e : ∀ (P : C ⥤ Type) (j : ℕ), CH.H (CategoryOfElements.π P ⋙ F) j ≃+ TH P F' j),
          (∀ {A B : C} (φ : A ⟶ B) (x : F.obj A), c B ((F.map φ).hom x) = (F'.map φ).hom (c A x)) ∧
          ∀ {Q P : C ⥤ Type} (u : Q ⟶ P) (m : CH.Mor (CategoryOfElements.π P ⋙ F) (CategoryOfElements.π Q ⋙ F) (RingHom.id R)),
            ∀ h : m.G = CategoryOfElements.map u, (∀ T x, HEq (m.τ T x) x) → ∀ j x, e Q j (m.pull j x) = tPull u F' j (e P j x) := by
  intro C _ R _ F
  refine ⟨ulF F, fun A => AddEquiv.ulift.symm, fun P j => (cmpE P F j).symm, fun φ x => rfl, ?_⟩
  intro Q P u m h hτ j x
  obtain ⟨G, τ, nat⟩ := m
  dsimp only at h hτ
  subst h
  have hτ' : τ = (elMor u F).τ := by
    funext T
    ext x
    exact eq_of_heq (hτ T x)
  subst hτ'
  apply (cmpE Q F j).symm.symm.injective
  obtain ⟨y, rfl⟩ := (cmpE P F j).surjective x
  simp only [AddEquiv.symm_symm, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  exact cmp_pull u F j y
