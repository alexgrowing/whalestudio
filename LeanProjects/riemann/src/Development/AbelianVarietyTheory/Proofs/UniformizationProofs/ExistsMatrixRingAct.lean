import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MatrixAction

variable {S : Scheme.{0}}

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in

theorem _root_.GlobalTheory.MatrixAction.comp_finsetProd {G : Over S} [GrpObj G] [IsCommMonObj G] {T T' : Over S}
    (a : T' ⟶ T) {κ : Type} (s : Finset κ) (x : κ → (T ⟶ G)) :
    a ≫ (∏ l ∈ s, x l) = ∏ l ∈ s, a ≫ x l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, comp_mul, ih]

theorem finsetProd_comp {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
    (f : G ⟶ H) [IsMonHom f] {T : Over S}
    {κ : Type} (s : Finset κ) (x : κ → (T ⟶ G)) : (∏ l ∈ s, x l) ≫ f = ∏ l ∈ s, x l ≫ f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MonObj.one_comp]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, MonObj.mul_comp, ih]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in

theorem _root_.GlobalTheory.MatrixAction.isMonHom_of_points {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    (h1 : ∀ T : Over S, (1 : T ⟶ G) ≫ f = 1)
    (hm : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  constructor
  · have := h1 (𝟙_ (Over S))
    simpa [Hom.one_def] using this
  · have := hm (G ⊗ G) (fst G G) (snd G G)
    simpa [Hom.mul_def] using this

section
variable {G : Over S} [GrpObj G] {O : Type} [Ring O] (ρ : RingAct G O)

theorem act_add (a b : O) : ρ.act (a + b) = ρ.act a * ρ.act b := ρ.map_add a b

theorem act_zero : ρ.act 0 = 1 := by
  have h := act_add ρ 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem act_sum [IsCommMonObj G] {κ : Type} (s : Finset κ) (x : κ → O) :
    ρ.act (∑ k ∈ s, x k) = ∏ k ∈ s, ρ.act (x k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [act_zero]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, act_add, ih]

end

theorem exists_matrix_ringAct : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (j : ℕ) (p : IsPowGrp G' G j) (O : Type) [Ring O] (ιG : RingAct G O), ∃ ι' : RingAct G' (Matrix (Fin j) (Fin j) O), (∀ (m : (Matrix (Fin j) (Fin j) O)) (i : Fin j), ι'.act m ≫ p.pr i = ∏ l, p.pr l ≫ ιG.act (m i l)) := by
  intro S G G' _ _ _ _ j p O _ ιG
  have hext : ∀ {T : Over S} {a b : T ⟶ G'}, (∀ i, a ≫ p.pr i = b ≫ p.pr i) → a = b :=
    fun h => p.lim.hom_ext fun i => h i.as
  have hp := p.hom
  have hι := ιG.hom
  let A : Matrix (Fin j) (Fin j) O → (G' ⟶ G') := fun m =>
    p.lim.lift (Fan.mk G' fun i => ∏ l, p.pr l ≫ ιG.act (m i l))
  have hA : ∀ m i, A m ≫ p.pr i = ∏ l, p.pr l ≫ ιG.act (m i l) := fun m i =>
    p.lim.fac (Fan.mk G' fun i => ∏ l, p.pr l ≫ ιG.act (m i l)) ⟨i⟩
  refine ⟨⟨A, fun m => ?_, ?_, fun a b => ?_, fun a b => ?_⟩, hA⟩
  · refine isMonHom_of_points _ (fun T => hext fun i => ?_) (fun T x y => hext fun i => ?_)
    · rw [Category.assoc, hA, comp_finsetProd, MonObj.one_comp (p.pr i)]
      refine Finset.prod_eq_one fun l _ => ?_
      rw [← Category.assoc, MonObj.one_comp, MonObj.one_comp]
    · rw [MonObj.mul_comp _ _ (p.pr i), Category.assoc, Category.assoc, Category.assoc, hA, comp_finsetProd,
        comp_finsetProd, comp_finsetProd, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [← Category.assoc, MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc]
  · refine hext fun i => ?_
    rw [hA, Category.id_comp, Finset.prod_eq_single i]
    · rw [Matrix.one_apply_eq, ιG.map_one, Category.comp_id]
    · intro l _ hl
      rw [Matrix.one_apply_ne hl.symm, act_zero, MonObj.comp_one]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · refine hext fun i => ?_
    rw [Category.assoc, hA, hA, comp_finsetProd]
    have e1 : ∀ k, A b ≫ p.pr k ≫ ιG.act (a i k)
        = ∏ l, p.pr l ≫ ιG.act (a i k * b k l) := fun k => by
      rw [← Category.assoc, hA, finsetProd_comp]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [ιG.map_mul, Category.assoc]
    rw [Finset.prod_congr rfl fun k _ => e1 k, Finset.prod_comm]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, act_sum, comp_finsetProd]
  · refine hext fun i => ?_
    change _ = (A a * A b) ≫ p.pr i
    rw [MonObj.mul_comp, hA, hA, hA, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [Matrix.add_apply, act_add, MonObj.comp_mul]

end GlobalTheory.MatrixAction
