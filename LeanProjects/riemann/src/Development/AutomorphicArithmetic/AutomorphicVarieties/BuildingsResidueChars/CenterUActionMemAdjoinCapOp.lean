import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GenGlRelationsAndCommuteOfIsLie
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LieMapEqSumIdempotentGen
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.centerU_action_mem_adjoin_capOp :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι), ∀ z ∈ (isExpLieAlgebra K n).centerU, uAction z ∈ Algebra.adjoin ℂ {x | ∃ τ u, x = capOp D n τ u} := by
  intro K _ _ n ι _ D z hz
  obtain ⟨hrel, hcomm⟩ := UpperTheory.gen_glRelations_and_commute_of_isLie (mixedSpace K) ι n _ D (lam K n) (isLie_lam K n)
  have h1 : ∀ u : UEnv K n,
      uAction u ∈ Algebra.adjoin ℂ {x | ∃ τ i j, x = gen D (lam K n) τ i j} := by
    intro u
    induction u using UEnv.induction with
    | halg r =>
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ℝ ℂ]
      exact Subalgebra.algebraMap_mem _ _
    | hι Y =>
      obtain ⟨X, rfl⟩ := (toLie K n).surjective Y
      rw [← lam_apply, UpperTheory.lieMap_eq_sum_idempotent_gen (mixedSpace K) ι n _ D (lam K n) X]
      exact sum_mem fun τ _ => sum_mem fun i _ => sum_mem fun j _ =>
        Subalgebra.smul_mem _ (Algebra.subset_adjoin (by exact ⟨τ, i, j, rfl⟩)) _
    | hmul x y hx hy => rw [map_mul]; exact mul_mem hx hy
    | hadd x y hx hy => rw [map_add]; exact add_mem hx hy
  refine UpperTheory.V.Fb.multiCentre (gen D (lam K n)) hrel hcomm (h1 z) fun τ i j => ?_
  have h2 := gen_mem D (lam K n) τ i j
    (Subalgebra.toSubmodule (Subalgebra.centralizer ℂ {uAction z})) fun x => by
      rintro _ rfl
      rw [lam_apply, ← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 hz]
  exact (h2 _ rfl).symm
