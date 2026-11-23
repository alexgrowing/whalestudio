import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.BCoreT

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem filtration_coaction_stable : FiltrationCoactionStable := by
  intro n _ M CF pi _ x hx l
  let L0 : (M.ι → ℤ) →+ (M.ι → ℤ) :=
    { toFun := fun x i => l (∑ k, M.A i k * (x k : GLCoord ℤ n))
      map_zero' := by funext i; simp
      map_add' := fun x y => by
        funext i
        simp only [Pi.add_apply, Int.cast_add, mul_add, sum_add_distrib, map_add] }
  let L : (M.ι → ℤ) →ₗ[ℤ] (M.ι → ℤ) := L0.toIntLinearMap
  have hL : CF.Mpi pi ≤ (CF.Mpi pi).comap L := by
    unfold ColFam.Mpi
    rw [Submodule.span_le]
    rintro y ⟨j, hj, I, rfl⟩
    have : L (CF.vec j I) = ∑ K, l (TMat (CF.mu j) K I) • CF.vec j K := by
      funext i
      have h1 : L (CF.vec j I) i = l (∑ k, M.A i k * (CF.ph j k I : GLCoord ℤ n)) := rfl
      rw [h1, qb_equiv_apply, map_sum, Finset.sum_apply]
      refine sum_congr rfl fun K _ => ?_
      rw [← zsmul_eq_mul, map_zsmul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
      rfl
    rw [SetLike.mem_coe, Submodule.mem_comap, this]
    exact Submodule.sum_mem _ fun K _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, K, rfl⟩)
  exact hL hx

end Formalism.InvariantFactorPaths.ColumnFamilies
