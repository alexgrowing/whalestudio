import Mathlib

universe u

namespace GlobalTheory.CompanionTheory.EisTube

theorem gaussInt : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c →
    MeasureTheory.Integrable (fun y : ι → ℝ => Real.exp (-(c * ∑ i, y i ^ 2))) := by
  intro ι _ c hc
  have h1 : MeasureTheory.Integrable (fun x : ℝ => Real.exp (-c * x ^ 2)) :=
    integrable_exp_neg_mul_sq hc
  have h2 := MeasureTheory.Integrable.fintype_prod (ι := ι) (f := fun _ x => Real.exp (-c * x ^ 2))
    (μ := fun _ => MeasureTheory.volume) (fun _ => h1)
  refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib, neg_mul]

end GlobalTheory.CompanionTheory.EisTube
