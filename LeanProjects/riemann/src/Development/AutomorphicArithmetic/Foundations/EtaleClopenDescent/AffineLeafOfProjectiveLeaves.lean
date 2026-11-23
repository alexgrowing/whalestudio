import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
import Development.AutomorphicArithmetic.CommutativeAlgebra.EquivOfAffineBijective
import Development.AutomorphicArithmetic.CommutativeAlgebra.EquivOfConstantSection
import Development.AutomorphicArithmetic.CommutativeAlgebra.RepresentedAffineBijective
import Development.AutomorphicArithmetic.CommutativeAlgebra.InclusionConnectedTwist
import Development.AutomorphicArithmetic.CommutativeAlgebra.ConnectedOfUnimodularSub
import Development.AutomorphicArithmetic.CommutativeAlgebra.NerveFirstProjection
import Development.AutomorphicArithmetic.CommutativeAlgebra.VectorBundleAffineRep
import Development.AutomorphicArithmetic.CommutativeAlgebra.NerveAffineRepresentable
import Development.AutomorphicArithmetic.CommutativeAlgebra.RepresentableOfAffine

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

namespace UpperTheory.Aff

variable (D : Type) [CommRing D]

private theorem eqv_comp' {R : Type} [CommRing R] (F : Shv R) {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'')
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have h : (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = pull R f F n ∘ pull R g F n := by
    funext x
    exact pull_comp R f g F n x
  rw [h]
  exact (hf n).comp (hg n)

private theorem eqv_id' {R : Type} [CommRing R] (F : Shv R) (E : Spc) : Eqv R (𝟙 E) F := by
  intro n
  have h : (pull R (𝟙 E) F n : H R E F n → H R E F n) = id := by
    funext x
    exact pull_id R E F n x
  rw [h]
  exact Function.bijective_id

private theorem sx_ext {X : RF} {n : SimplexCategoryᵒᵖ} {U : Schemeᵒᵖ} {x y : ((CN X).obj n).obj U}
    (h : ∀ i, x.1 i = y.1 i) : x = y := Subtype.ext (funext h)

private theorem vec_ext {N : ℕ} {A : Type} [CommRing A] {x y : (Vec D N).obj A} (h : x.1 = y.1) : x = y := Subtype.ext h

private theorem ratio1_rel (d : ℕ) {A : Type} [CommRing A] {x y : (L1 D d).obj A}
    (h : (ratio1 D d).app A x = (ratio1 D d).app A y) : (L1 D d).rel x y := by
  obtain ⟨ux, hx⟩ : IsUnit (x.1.1.2 (Fin.last d)) := x.2
  obtain ⟨uy, hy⟩ : IsUnit (y.1.1.2 (Fin.last d)) := y.2
  refine ⟨congrArg (fun z : (D →+* A) × (Fin d → A) => z.1) h, ux * uy⁻¹, funext fun j => ?_⟩
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [← hx, ← hy]
    simp
  · have hj : x.1.1.2 j.castSucc * Ring.inverse (x.1.1.2 (Fin.last d)) =
        y.1.1.2 j.castSucc * Ring.inverse (y.1.1.2 (Fin.last d)) :=
      congrFun (congrArg (fun z : (D →+* A) × (Fin d → A) => z.2) h) j
    rw [← hx, ← hy, Ring.inverse_unit, Ring.inverse_unit] at hj
    have h1 : (ux : A) * ((ux⁻¹ : Aˣ) : A) = 1 := Units.mul_inv ux
    simp only [Units.val_mul]
    linear_combination (-(x.1.1.2 j.castSucc)) * h1 + (ux : A) * hj

private theorem ratio_comp_section_eq (d : ℕ) {A : Type} [CommRing A] (m : (Aff D d).obj A) :
    (ratio1 D d).app A ((sec1 D d).app A m) = m := by
  refine Prod.ext rfl (funext fun j => ?_)
  change Fin.snoc (α := fun _ => A) m.2 1 j.castSucc *
    Ring.inverse (Fin.snoc (α := fun _ => A) m.2 1 (Fin.last d)) = m.2 j
  simp

private def sectionAppendOne (d : ℕ) : (Vec D d).Hom (lift_levelP_alt₂ D d) where
  app A _ x := ⟨((sec1 D d).app A x.1).1, by
    refine ⟨?_, ((sec1 D d).app A x.1).2⟩
    change Ideal.span (Set.range fun j : Fin d => Fin.snoc (α := fun _ => A) x.1.2 1 j.castSucc) = ⊤
    simpa using x.2⟩
  nat {A B} _ _ f x := by
    have h := (sec1 D d).nat f x.1
    exact Subtype.ext (congrArg (fun z : (L1 D d).obj B => z.1) h)

private theorem eqv_fstV (hH : LeafHI) (a3 : A3) (b3 : B3) (c4 : C4) (q : ℕ) [NeZero q] (i : ℤ) (d : ℕ)
    (hq : IsUnit (q : D)) : Eqv _ (CN.map (fstV D d) (fstV_rel D d)) (tw q i) := by
  refine a3 _ _ _ fun n => ?_
  obtain ⟨Y, a, φ, hφ⟩ := UpperTheory.nerve_affine_representable D d n
  have hY : IsUnit (q : Γ(Y, ⊤)) := by simpa using hq.map a
  exact UpperTheory.representable_of_affine hH b3 c4 q i ((CN.map (fstV D d) (fstV_rel D d)).app n)
    (fun T x => (x.1 0).1.1.2 (Fin.last d)) (fun f x => rfl) (fun T => UpperTheory.nerve_first_projection D d n T) Y hY φ hφ

private theorem inclusion_two_first_vector (d : ℕ) : CN.map (incl2 D d) (inclusion_two_relation D d) ≫ CN.map (fstV D d) (fstV_rel D d) = 𝟙 _ := by
  refine NatTrans.ext (funext fun n => NatTrans.ext (funext fun U => ?_))
  have key : ∀ {A : Type} [CommRing A] (y : (Vec D d).obj A), (fstV D d).app A ((incl2 D d).app A y) = y := by
    intro A _ y
    refine vec_ext D (Prod.ext rfl (funext fun j => ?_))
    change Fin.snoc (α := fun _ => A) y.1.2 0 j.castSucc = y.1.2 j
    simp
  exact ConcreteCategory.hom_ext _ _ fun x => sx_ext (X := Vec D d) (n := n) (U := U) fun i => key (x.1 i)

private theorem inclusion_two_comp_identity (d : ℕ) : CN.map (incl D d) (incl_rel D d) ≫ 𝟙 _ =
    CN.map (incl2 D d) (inclusion_two_relation D d) ≫ CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map) := by
  rw [Category.comp_id]
  rfl

private theorem final_square (a1 : A1) {R : Type} [CommRing R] (F : Shv R) (d : ℕ)
    (U : (Spec (CommRingCat.of (MvPolynomial (Fin d) D))).Opens)
    (hU : IsCompl' (varIdeal (RingHom.id (MvPolynomial (Fin d) D))) U) :
    ∃ (r1 : CN (L1 D d) ⟶ sch.obj (Spec (CommRingCat.of (MvPolynomial (Fin d) D)))) (r2 : CN (lift_levelP_alt₂ D d) ⟶ sch.obj U),
      Eqv R r1 F ∧ Eqv R r2 F ∧ CN.map (bothToFirst D d) (both_to_first_relation D d) ≫ r1 = r2 ≫ sch.map U.ι := by
  obtain ⟨φ, hφ1, hφ2⟩ := UpperTheory.vector_bundle_affine_rep D d U hU
  refine ⟨CN.proj (ratio1 D d) (ratio1_const D d) ≫ disc.map (repA D d),
    CN.proj (ratioBoth D d) (ratio_both_constant D d) ≫ disc.map φ, ?_, ?_, ?_⟩
  · refine eqv_comp' F _ _ ?_ (UpperTheory.equiv_of_affine_bijective R F _ fun T _ => UpperTheory.represented_affine_bijective D d T)
    exact UpperTheory.equiv_of_constant_section a1 R F _ _ (fun h => ratio1_rel D d h) (sec1 D d) (fun m => ratio_comp_section_eq D d m)
  · refine eqv_comp' F _ _ ?_ (UpperTheory.equiv_of_affine_bijective R F _ hφ2)
    refine UpperTheory.equiv_of_constant_section a1 R F _ _ (fun {A} _ {x y} h => ?_) (sectionAppendOne D d) (fun {A} _ m => ?_)
    · exact ratio1_rel D d (x := (bothToFirst D d).app A x) (y := (bothToFirst D d).app A y)
        (congrArg Subtype.val h)
    · exact Subtype.ext (ratio_comp_section_eq D d m.1)
  · refine NatTrans.ext (funext fun n => NatTrans.ext (funext fun T => ?_))
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    have h := hφ1 T.unop ((ratioBoth D d).app _ (x.1 0))
    exact h.symm

end UpperTheory.Aff

theorem UpperTheory.Cb.affine_leaf_of_projective_leaves :
    LateralTheory.E.t_E6Cut.LeafProj → LateralTheory.E.t_E6Cut.LeafExc → LateralTheory.E.t_E6Cut.LeafHI → LateralTheory.E.t_E6Cut.LeafAff := by
  intro hP hE hH a1 a3 a5 a7 a9 a10 b3 c4 d1 q _ i d D _ hq U hU
  have h1 := UpperTheory.inclusion_connected_twist hP a1 a5 a7 a9 a10 d1 q i d D hq
  have ht := eqv_section (tw q i) _ _ (inclusion_two_first_vector D d) (eqv_fstV D hH a3 b3 c4 q i d hq)
  have hf := (conn_sq (tw q i) (2 * (d : ℤ)) _ _ _ _ (inclusion_two_comp_identity D d) ht (eqv_id' _ _)).1 h1
  have hg := UpperTheory.connected_of_unimodular_sub hE a1 _ (tw q i) _ d D hf
  obtain ⟨r1, r2, e1, e2, hc⟩ := final_square D a1 (tw q i) d U hU
  exact (conn_sq (tw q i) _ _ _ _ _ hc e2 e1).1 hg
