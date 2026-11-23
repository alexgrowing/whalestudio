import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupRingConst

noncomputable def pt {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) : AddMonoidAlgebra R X →+* F :=
  AddMonoidAlgebra.liftNCRingHom r ((Units.coeHom F).comp c) (fun _ _ ↦ Commute.all _ _)

@[simp] lemma pt_single {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) (a : X) (x : R) :
    pt r c (AddMonoidAlgebra.single a x) = r x * (c (Multiplicative.ofAdd a) : F) := by
  simp [pt, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]

lemma pt_comp_algebraMap {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) :
    (pt r c).comp (algebraMap R (AddMonoidAlgebra R X)) = r := by
  ext x
  simp [AddMonoidAlgebra.coe_algebraMap, pt_single]

def powChar {G X : Type} [CommGroup G] [AddCommGroup X] (l : X →+ ℤ) (u : G) :
    Multiplicative X →* G :=
  (zpowersHom G u).comp (AddMonoidHom.toMultiplicative l)

@[simp] lemma powChar_apply {G X : Type} [CommGroup G] [AddCommGroup X] (l : X →+ ℤ) (u : G)
    (a : X) : powChar l u (Multiplicative.ofAdd a) = u ^ l a := by
  simp [powChar]

lemma eq_prod_powChar {G X I : Type} [CommGroup G] [AddCommGroup X] [Fintype I]
    (b : Module.Basis I ℤ X) (c : Multiplicative X →* G) :
    c = ∏ i, powChar (b.coord i).toAddMonoidHom (c (Multiplicative.ofAdd (b i))) := by
  refine MonoidHom.ext fun m => ?_
  obtain ⟨a, rfl⟩ : ∃ a, Multiplicative.ofAdd a = m := ⟨Multiplicative.toAdd m, rfl⟩
  rw [MonoidHom.finsetProd_apply]
  simp only [powChar_apply]
  conv_lhs => rw [← b.sum_repr a]
  rw [ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_zsmul, map_zpow]
  simp [Module.Basis.coord_apply]

noncomputable def family {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) (l : X →+ ℤ) : AddMonoidAlgebra R X →+* AddMonoidAlgebra F ℤ :=
  AddMonoidAlgebra.liftNCRingHom ((algebraMap F (AddMonoidAlgebra F ℤ)).comp r)
    (((algebraMap F (AddMonoidAlgebra F ℤ)).toMonoidHom.comp ((Units.coeHom F).comp c)) *
      ((AddMonoidAlgebra.of F ℤ).comp (AddMonoidHom.toMultiplicative l)))
    (fun _ _ ↦ Commute.all _ _)

lemma family_single {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) (l : X →+ ℤ) (a : X) (x : R) :
    family r c l (AddMonoidAlgebra.single a x) =
      AddMonoidAlgebra.single (l a) (r x * (c (Multiplicative.ofAdd a) : F)) := by
  simp [family, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single,
    AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.of_apply, _root_.mul_assoc]

lemma family_comp_algebraMap {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X]
    (r : R →+* F) (c : Multiplicative X →* Fˣ) (l : X →+ ℤ) :
    (family r c l).comp (algebraMap R (AddMonoidAlgebra R X)) =
      (algebraMap F (AddMonoidAlgebra F ℤ)).comp r := by
  ext x
  simp [AddMonoidAlgebra.coe_algebraMap, family_single]

lemma pt_comp_family {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X]
    (r : R →+* F) (c : Multiplicative X →* Fˣ) (l : X →+ ℤ) (u : Fˣ) :
    (pt (RingHom.id F) (zpowersHom Fˣ u)).comp (family r c l) = pt r (c * powChar l u) := by
  refine AddMonoidAlgebra.ringHom_ext (fun x => ?_) (fun a => ?_) <;>
    (rw [RingHom.comp_apply, family_single, pt_single, pt_single]
     simp [powChar_apply])

lemma spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B)
    (ψ : B →+* C) : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

private lemma powChar_one {G X : Type} [CommGroup G] [AddCommGroup X] (l : X →+ ℤ) :
    GlobalTheory.GroupRingConst.powChar l (1 : G) = 1 := by
  refine MonoidHom.ext fun m => ?_
  rw [MonoidHom.one_apply, ← ofAdd_toAdd m, GlobalTheory.GroupRingConst.powChar_apply, one_zpow]

private lemma pt_eq_lemma_2 {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X]
    (φ : AddMonoidAlgebra R X →+* F) :
    φ = GlobalTheory.GroupRingConst.pt (φ.comp (algebraMap R (AddMonoidAlgebra R X)))
      ((φ.toMonoidHom.comp (AddMonoidAlgebra.of R X)).toHomUnits) := by
  refine AddMonoidAlgebra.ringHom_ext (fun x => ?_) (fun a => ?_)
  · simp [GlobalTheory.GroupRingConst.pt_single, AddMonoidAlgebra.coe_algebraMap]
  · simp [GlobalTheory.GroupRingConst.pt_single, MonoidHom.coe_toHomUnits, AddMonoidAlgebra.of_apply]
    rw [← map_mul, AddMonoidAlgebra.single_mul_single, zero_add, _root_.one_mul]

private lemma step_lemma_3 {S Y : Scheme.{0}} (p : Y ⟶ S)
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    {R X : Type} [CommRing R] [AddCommGroup X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s)
    (L : Type) [Field L] (r : R →+* L) (c : Multiplicative X →* Lˣ) (l : X →+ ℤ) (u : Lˣ) :
    Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r (c * GlobalTheory.GroupRingConst.powChar l u))) ≫ f =
      Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r c)) ≫ f := by
  obtain ⟨k, hk⟩ := h L (Spec.map (CommRingCat.ofHom r) ≫ s)
    (Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.family r c l)) ≫ f) (by
      rw [Category.assoc, hf, ← Category.assoc, GlobalTheory.GroupRingConst.spec_comp, GlobalTheory.GroupRingConst.family_comp_algebraMap, ← GlobalTheory.GroupRingConst.spec_comp,
        Category.assoc])
  have key : ∀ v : Lˣ, Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r (c * GlobalTheory.GroupRingConst.powChar l v))) ≫ f = k := by
    intro v
    rw [← GlobalTheory.GroupRingConst.pt_comp_family, ← GlobalTheory.GroupRingConst.spec_comp, Category.assoc, hk, ← Category.assoc, GlobalTheory.GroupRingConst.spec_comp,
      GlobalTheory.GroupRingConst.pt_comp_algebraMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have h1 := key 1
  rw [powChar_one, _root_.mul_one] at h1
  rw [key u, h1]

private lemma chain_lemma_4 {S Y : Scheme.{0}} (p : Y ⟶ S)
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    {R X : Type} [CommRing R] [AddCommGroup X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s) [Module.Free ℤ X] [Module.Finite ℤ X]
    (L : Type) [Field L] (r : R →+* L) (c : Multiplicative X →* Lˣ) :
    Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r c)) ≫ f = Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r 1)) ≫ f := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  have key : ∀ t : Finset (Module.Free.ChooseBasisIndex ℤ X),
      Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r (∏ i ∈ t,
        GlobalTheory.GroupRingConst.powChar (b.coord i).toAddMonoidHom (c (Multiplicative.ofAdd (b i)))))) ≫ f =
      Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r 1)) ≫ f := by
    intro t
    induction t using Finset.induction_on with
    | empty => rw [Finset.prod_empty]
    | @insert i t hi ih =>
      rw [Finset.prod_insert hi, _root_.mul_comm (GlobalTheory.GroupRingConst.powChar _ _), step_lemma_3 p h s f hf, ih]
  conv_lhs => rw [GlobalTheory.GroupRingConst.eq_prod_powChar b c]
  exact key Finset.univ

private lemma pts_lemma_5 {S Y : Scheme.{0}} (p : Y ⟶ S)
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    {R X : Type} [CommRing R] [AddCommGroup X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s) [Module.Free ℤ X] [Module.Finite ℤ X]
    (L : Type) [Field L] (φ : AddMonoidAlgebra R X →+* L) :
    Spec.map (CommRingCat.ofHom φ) ≫ f = Spec.map (CommRingCat.ofHom φ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫
        Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt (RingHom.id R) 1)) ≫ f := by
  rw [← Category.assoc, ← Category.assoc, GlobalTheory.GroupRingConst.spec_comp, GlobalTheory.GroupRingConst.spec_comp]
  have e1 : (φ.comp (algebraMap R (AddMonoidAlgebra R X))).comp
      (GlobalTheory.GroupRingConst.pt (RingHom.id R) (1 : Multiplicative X →* Rˣ)) =
      GlobalTheory.GroupRingConst.pt (φ.comp (algebraMap R (AddMonoidAlgebra R X))) (1 : Multiplicative X →* Lˣ) := by
    refine AddMonoidAlgebra.ringHom_ext (fun x => ?_) (fun a => ?_) <;> simp [GlobalTheory.GroupRingConst.pt_single]
  rw [e1]
  conv_lhs => rw [pt_eq_lemma_2 φ]
  exact chain_lemma_4 p h s f hf L _ _

end GlobalTheory.GroupRingConst

open GlobalTheory.GroupRingConst in
theorem GlobalTheory.groupRing_hom_const_of_laurent {S Y : Scheme.{0}} (p : Y ⟶ S) [IsSeparated p]
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    (R : Type) [CommRing R] [IsDomain R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s) :
    ∃ k : Spec (CommRingCat.of R) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ k := by
  classical
  have : UniqueSums X := UniqueSums.of_injective_addHom
    (Module.Free.chooseBasis ℤ X).repr.toLinearMap.toAddMonoidHom.toAddHom
    (Module.Free.chooseBasis ℤ X).repr.injective inferInstance
  have hcomp : (pt (RingHom.id R) (1 : Multiplicative X →* Rˣ)).comp
      (algebraMap R (AddMonoidAlgebra R X)) = RingHom.id R := pt_comp_algebraMap _ _
  refine ⟨Spec.map (CommRingCat.ofHom (pt (RingHom.id R) 1)) ≫ f, ?_⟩
  refine ext_of_fromSpecResidueField_eq _ _ p Set.univ dense_univ (fun x _ => ?_) ?_
  · obtain ⟨φ, hφ⟩ : ∃ φ : AddMonoidAlgebra R X →+*
        ((Spec (CommRingCat.of (AddMonoidAlgebra R X))).residueField x),
        Spec.map (CommRingCat.ofHom φ) = (Spec (CommRingCat.of (AddMonoidAlgebra R X))).fromSpecResidueField x :=
      ⟨(Spec.preimage ((Spec (CommRingCat.of (AddMonoidAlgebra R X))).fromSpecResidueField x)).hom,
        by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
    rw [← hφ]
    exact pts_lemma_5 p h s f hf _ φ
  · rw [hf, Category.assoc, Category.assoc, hf,
      ← Category.assoc _ (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X)))), spec_comp, hcomp,
      CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
