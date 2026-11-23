import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits groupCohomology Rep

universe v w u

section HomComplex

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

noncomputable def linearYonedaObjMap {X Y : ChainComplex C ℕ} (f : X ⟶ Y) (B : C) :
    Y.linearYonedaObj R B ⟶ X.linearYonedaObj R B :=
  (HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map
    ((((linearYoneda R C).obj B).rightOp.mapHomologicalComplex _).map f).op

lemma linearYonedaObjMap_f_apply {X Y : ChainComplex C ℕ} (f : X ⟶ Y) (B : C) (n : ℕ)
    (x : Y.X n ⟶ B) : (linearYonedaObjMap (R := R) f B).f n x = f.f n ≫ x := rfl

lemma linearYonedaObjMap_comp {X Y Z : ChainComplex C ℕ} (f : X ⟶ Y) (g : Y ⟶ Z) (B : C) :
    linearYonedaObjMap (R := R) (f ≫ g) B = linearYonedaObjMap g B ≫ linearYonedaObjMap f B := by
  ext n x
  change (f ≫ g).f n ≫ x = f.f n ≫ g.f n ≫ x
  rw [HomologicalComplex.comp_f]
  exact Category.assoc _ _ _

lemma linearYonedaObjMap_id (X : ChainComplex C ℕ) (B : C) :
    linearYonedaObjMap (R := R) (𝟙 X) B = 𝟙 _ := by
  ext n x
  change (𝟙 X : X ⟶ X).f n ≫ x = x
  rw [HomologicalComplex.id_f]
  exact Category.id_comp _

noncomputable def linearYonedaObjHomotopy {X Y : ChainComplex C ℕ} {f g : X ⟶ Y}
    (h : Homotopy f g) (B : C) :
    Homotopy (linearYonedaObjMap (R := R) f B) (linearYonedaObjMap g B) :=
  ((((linearYoneda R C).obj B).rightOp).mapHomotopy h).unop

noncomputable def linearYonedaObjHomotopyEquiv {X Y : ChainComplex C ℕ} (e : HomotopyEquiv X Y)
    (B : C) : HomotopyEquiv (Y.linearYonedaObj R B) (X.linearYonedaObj R B) where
  hom := linearYonedaObjMap e.hom B
  inv := linearYonedaObjMap e.inv B
  homotopyHomInvId := (Homotopy.ofEq (linearYonedaObjMap_comp _ _ _).symm).trans
    ((linearYonedaObjHomotopy e.homotopyInvHomId B).trans
      (Homotopy.ofEq (linearYonedaObjMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (linearYonedaObjMap_comp _ _ _).symm).trans
    ((linearYonedaObjHomotopy e.homotopyHomInvId B).trans
      (Homotopy.ofEq (linearYonedaObjMap_id _ _)))

end HomComplex

section Bar

variable {k G : Type u} [CommRing k] [Group G]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

lemma diagonalSuccIsoFree_inv_single (m : ℕ) (f : Fin m → G) (g : G) (r : k) :
    (diagonalSuccIsoFree k G m).inv.hom (Finsupp.single f (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd f) r := by
  simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  have step1 : (Hom.hom (leftRegularTensorTrivialIsoFree k G (Fin m → G)).inv)
      (Finsupp.single f (.single g r)) = .single g 1 ⊗ₜ[k] .single f r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single f g r
  rw [step1]
  simp only [mkIso_inv, Representation.linearizeOfMulActionIso, Representation.Equiv.mk_symm,
    LinearEquiv.refl_symm, ConcreteCategory.hom_ofHom, Action.tensorObj_V, Action.trivial_V,
    Functor.mapIso_inv, tensor_V, tensor_ρ, Iso.symm_inv, Functor.Monoidal.μIso_hom, μ_hom,
    MonoidalCategory.tensorIso_inv, Representation.linearizeTrivialIso, hom_tensorHom,
    Representation.IntertwiningMap.tensor_apply, Representation.Equiv.coe_toIntertwiningMap,
    Representation.Equiv.mk_apply, LinearEquiv.refl_apply]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G m).inv (g, f) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin m → G)) g f 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G m).inv) z) key₂).trans key₁).trans (by simp)

lemma barResolution_π_f_zero_single (v : Fin 0 → G) (g : G) (r : k) :
    ((barResolution k G).π.f 0).hom (Finsupp.single v (MonoidAlgebra.single g r)) = r := by
  change (standardComplex.ε k G).hom ((diagonalSuccIsoFree k G 0).inv.hom
    (Finsupp.single v (MonoidAlgebra.single g r))) = r
  rw [diagonalSuccIsoFree_inv_single]
  simp [standardComplex.ε]

end Bar

section Norm

variable {k H : Type u} [CommRing k] [Group H] [Fintype H]

lemma ρ_apply_norm (B : Rep.{u} k H) (b : B) (s : H) : B.ρ s (B.ρ.norm b) = B.ρ.norm b := by
  rw [Representation.norm, LinearMap.sum_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun t => ?_
  simp [← Module.End.mul_apply, ← map_mul]

end Norm

end GroundTheory.GroupCoh
