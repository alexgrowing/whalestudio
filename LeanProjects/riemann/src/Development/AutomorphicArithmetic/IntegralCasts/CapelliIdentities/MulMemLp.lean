import Mathlib

theorem UpperTheory.Reformulated.B.Qf3.mul_memLp.{u_1} :
    ∀ {X : Type u_1}
    [inst : MeasurableSpace X] {ν : MeasureTheory.Measure X} (c : X → ℝ),
    Measurable c →
      (∀ (x : X), |c x| ≤ (1 : ℝ)) →
        ∀ (f : ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν)),
          MeasureTheory.MemLp (fun (x : X) ↦ (↑(c x) : ℂ) * (↑(↑f : X →ₘ[ν] ℂ) : X → ℂ) x) (2 : ENNReal) ν := by
  intro X _ ν c hc hb f
  refine MeasureTheory.MemLp.of_le (MeasureTheory.Lp.memLp f) ?_ ?_
  · exact (Complex.measurable_ofReal.comp hc).aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable f)
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb x)
