import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartPointSeparable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

namespace ChartParAlgebraic

theorem proof : ChartParAlgebraic.Statement := by
  intro F _ n e K L _ _ _ _ _ _ u t η hu hη hrel hchart j₀ hη0
  generalize hz : (fun m => η m * (η j₀)⁻¹) = z
  have hzm : ∀ m, z m = η m * (η j₀)⁻¹ := fun m => by rw [← hz]
  have hz0 : z j₀ = 1 := by rw [hzm, mul_inv_cancel₀ hη0]
  set A₀ := Algebra.adjoin F (Set.range z) with hA₀
  set B := Algebra.adjoin A₀ (Set.range fun p : Fin e × {j : Fin n // j ≠ j₀} =>
    algebraMap K L (u (p.1, p.2.1))) with hB
  have hzB : ∀ m, z m ∈ B := fun m =>
    Subalgebra.algebraMap_mem B (⟨z m, Algebra.subset_adjoin ⟨m, rfl⟩⟩ : A₀)
  have hwB : ∀ p : Fin e × {j : Fin n // j ≠ j₀}, algebraMap K L (u (p.1, p.2.1)) ∈ B :=
    fun p => Algebra.subset_adjoin ⟨p, rfl⟩
  have hFB : ∀ c : F, algebraMap F L c ∈ B := fun c => by
    rw [IsScalarTower.algebraMap_apply F A₀ L]
    exact Subalgebra.algebraMap_mem B _
  have huB : ∀ p : Fin e × Fin n, algebraMap K L (u p) ∈ B := by
    rintro ⟨i, j⟩
    by_cases hj : j = j₀
    · rw [hj]
      have hsum : ∑ j, algebraMap K L (u (i, j)) * z j = 0 := by
        simp only [hzm, ← mul_assoc, ← Finset.sum_mul, hrel i, zero_mul]
      have h1 := Finset.add_sum_erase Finset.univ (fun j => algebraMap K L (u (i, j)) * z j)
        (Finset.mem_univ j₀)
      simp only [hz0, mul_one] at h1
      rw [hsum, ← eq_neg_iff_add_eq_zero] at h1
      rw [h1]
      refine neg_mem (Subalgebra.sum_mem _ fun j' hj' => Subalgebra.mul_mem _ ?_ (hzB j'))
      exact hwB (i, ⟨j', Finset.ne_of_mem_erase hj'⟩)
    · exact hwB (i, ⟨j, hj⟩)
  have hmem : ∀ b ∈ B, IsAlgebraic B b := fun b hb => isAlgebraic_algebraMap (⟨b, hb⟩ : B)
  have hη0alg : IsAlgebraic B (η j₀) := by
    have hs : ∑ m, algebraMap F L (t m) * z m = (η j₀)⁻¹ := by
      simp only [hzm, ← mul_assoc, ← Finset.sum_mul, hchart, one_mul]
    have h2 : IsAlgebraic B (∑ m, algebraMap F L (t m) * z m) :=
      hmem _ (Subalgebra.sum_mem _ fun m _ => Subalgebra.mul_mem _ (hFB (t m)) (hzB m))
    have := h2.inv
    rwa [hs, inv_inv] at this
  have hηalg : ∀ m, IsAlgebraic B (η m) := fun m => by
    have hm : η m = z m * η j₀ := by rw [hzm, inv_mul_cancel_right₀ hη0]
    rw [hm]
    exact (hmem _ (hzB m)).mul hη0alg
  have hK : ∀ c : K, IsAlgebraic B (algebraMap K L c) := fun c => by
    have hc : c ∈ IntermediateField.adjoin F (Set.range u) := by rw [hu]; trivial
    induction hc using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact hmem _ (huB p)
    | algebraMap x =>
      rw [← IsScalarTower.algebraMap_apply F K L]
      exact hmem _ (hFB x)
    | add x y _ _ hx hy =>
      rw [map_add]
      exact hx.add hy
    | inv x _ hx =>
      rw [map_inv₀]
      exact hx.inv
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact hx.mul hy
  refine ⟨fun y => ?_⟩
  have hy : y ∈ IntermediateField.adjoin K (Set.range η) := by rw [hη]; trivial
  induction hy using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact hηalg m
  | algebraMap x => exact hK x
  | add x y _ _ hx hy => exact hx.add hy
  | inv x _ hx => exact hx.inv
  | mul x y _ _ hx hy => exact hx.mul hy

end ChartParAlgebraic

end

end GroundTheory.Heights₂.Heights
