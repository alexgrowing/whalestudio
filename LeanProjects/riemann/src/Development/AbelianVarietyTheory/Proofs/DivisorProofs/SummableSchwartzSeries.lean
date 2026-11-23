import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace

open Filter
open scoped SchwartzMap Topology

namespace GlobalTheory
namespace SchwartzSum

theorem hasSum_of_summable_seminorms :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {ι : Type}
    (u : ι → SchwartzMap V ℂ), (∀ k n : ℕ, Summable (fun i => SchwartzMap.seminorm ℂ k n (u i))) →
    ∃ F : SchwartzMap V ℂ, (∀ x, HasSum (fun i => u i x) (F x)) ∧
      ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, HasSum (fun i => T (u i)) (T F) := by
  intro V _ _ _ ι u hu
  have hS : Summable u := by
    rw [summable_iff_vanishing]
    intro e he
    obtain ⟨⟨S, r⟩, hr, hsub⟩ := (schwartz_withSeminorms ℂ V ℂ).hasBasis_zero_ball.mem_iff.1 he
    simp only at hr hsub
    have hg : Summable (fun i => ∑ kn ∈ S, schwartzSeminormFamily ℂ V ℂ kn (u i)) :=
      summable_sum fun kn _ => hu kn.1 kn.2
    obtain ⟨s, hs⟩ := (summable_iff_vanishing_norm.1 hg) r hr
    refine ⟨s, fun t ht => hsub ?_⟩
    rw [Seminorm.mem_ball_zero]
    have h1 := hs t ht
    calc (S.sup (schwartzSeminormFamily ℂ V ℂ)) (∑ i ∈ t, u i)
        ≤ ∑ kn ∈ S, schwartzSeminormFamily ℂ V ℂ kn (∑ i ∈ t, u i) :=
          Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => apply_nonneg _ _) fun kn hkn =>
            Finset.single_le_sum (f := fun kn => schwartzSeminormFamily ℂ V ℂ kn (∑ i ∈ t, u i))
              (fun _ _ => apply_nonneg _ _) hkn
      _ ≤ ∑ kn ∈ S, ∑ i ∈ t, schwartzSeminormFamily ℂ V ℂ kn (u i) :=
          Finset.sum_le_sum fun kn _ =>
            Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _
      _ = ∑ i ∈ t, ∑ kn ∈ S, schwartzSeminormFamily ℂ V ℂ kn (u i) := Finset.sum_comm
      _ ≤ ‖∑ i ∈ t, ∑ kn ∈ S, schwartzSeminormFamily ℂ V ℂ kn (u i)‖ := Real.le_norm_self _
      _ < r := h1
  refine ⟨∑' i, u i, fun x => ?_, fun T => hS.hasSum.mapL T⟩
  have h := hS.hasSum.mapL ((BoundedContinuousFunction.evalCLM ℂ x).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ))
  simpa using h

end SchwartzSum
end GlobalTheory
