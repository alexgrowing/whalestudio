import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsSymmRelabel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR

universe u v w

theorem intNum_comp_perm {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) {n : ℕ} (bs : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)) :
    intNum F P (bs ∘ σ) = intNum F P bs := by
  unfold intNum
  rw [FieldNumbers.mixedDiff_comp_perm]

theorem SymmStatement.of_type (F : Type u) [Field F] {K : Type} [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] : SymmStatement F ι := by
  classical
  intro I hI V n L σ hV
  have hA : ∀ L' : Fin n → K → ℤ, I V n L' = intNum F V L' := fun L' =>
    Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full I hI V n L' hV
  rw [hA (L ∘ σ), hA L]
  exact intNum_comp_perm V L σ

theorem SymmStatement.of_found (hR : SymmRelabel.Statement.{u, v, w, 0, 0}) {K : Type v}
    [Fintype K] (F : Type u) [Field F] (ι : K → Type w) [∀ k, Fintype (ι k)] :
    SymmStatement F ι := by
  classical
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  refine hR F K ι (Fin (Fintype.card K)) (fun j => Fin (Fintype.card (ι (e.symm j)))) e
    (fun k => (Fintype.equivFin (ι k)).trans (finCongr ?_)) (SymmStatement.of_type F _)
  exact congrArg (fun x => Fintype.card (ι x)) (e.symm_apply_apply k).symm

end GroundTheory.Heights₂.Heights.Targets
