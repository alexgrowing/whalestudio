import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoOfBijectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.MonoOfInjectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.SimplicesPullbackExistsUniqueOfMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClassesStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.LHOne

variable {q : ℕ} {X : Spc}

private theorem cast_cast {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'')
    (x : Ht q X n i) : (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4
  rfl

private theorem cup_one' [NeZero q] (hX : Inv q X) {n i : ℤ} (x : Ht q X n i) :
    cup q x (one q X) = x.cast (by ring) (by ring) := by
  rw [GlobalTheory.T.tateTwistCupProduct_graded_comm q X x (one q X), (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 X hX x, cast_cast, mul_zero, Int.negOnePow_zero, one_smul]

private theorem bij_iff [NeZero q] {E : Spc} (π : X ⟶ E) (hX : Inv q X) {n i n' i' : ℤ} (hn : n' = n) (hi : i' = i)
    (h1 : n' + 0 = n) (h2 : i' + 0 = i) :
    Function.Bijective (fun a : Fin 1 → Ht q E n' i' =>
        ∑ j, ((cup q (pull _ π _ _ (a j)) (one q X)).cast h1 h2 : Ht q X n i)) ↔
      Function.Bijective (pull _ π (tw q i) n) := by
  subst hn hi
  have key : (fun a : Fin 1 → Ht q E n' i' =>
      ∑ j, ((cup q (pull _ π _ _ (a j)) (one q X)).cast h1 h2 : Ht q X n' i')) =
      (pull _ π (tw q i') n') ∘ (Equiv.funUnique (Fin 1) (Ht q E n' i')) := by
    funext a
    simp only [Fin.sum_univ_one, Function.comp_apply, Equiv.funUnique_apply]
    rw [cup_one' hX, cast_cast]
    rfl
  rw [key, Equiv.bijective_comp]

end UpperTheory.LHOne

theorem UpperTheory.lerayHirsch_one_iff_twist_equiv :
    ∀ (q : ℕ) [NeZero q] {X E : Spc} (π : X ⟶ E), Inv q X →
        (LH q π (fun _ : Fin 1 => (0 : ℤ)) (fun _ : Fin 1 => (0 : ℤ)) (fun _ => one q X) ↔ ∀ i, Eqv _ π (tw q i)) := by
  intro q _ X E π hX
  constructor
  · intro h i n
    exact (UpperTheory.LHOne.bij_iff π hX (sub_zero n) (sub_zero i) _ _).1 (h n i)
  · intro h n i
    exact (UpperTheory.LHOne.bij_iff π hX (sub_zero n) (sub_zero i) _ _).2 (h i n)
