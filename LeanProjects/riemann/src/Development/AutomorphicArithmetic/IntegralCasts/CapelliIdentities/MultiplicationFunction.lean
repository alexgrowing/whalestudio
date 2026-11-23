import Mathlib

noncomputable def UpperTheory.Reformulated.B.MultiplicationFunction.mulFn.{u_1} :
    {X : Type u_1} →
      [inst : MeasurableSpace X] →
        {ν : MeasureTheory.Measure X} →
          (c : X → ℝ) →
            Measurable c →
              (∀ (x : X), |c x| ≤ (1 : ℝ)) → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν) → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν) :=
  fun {X} _ {ν} c hc hb f =>
    MeasureTheory.MemLp.toLp (fun x : X => (c x : ℂ) * f x)
      (MeasureTheory.MemLp.of_le (MeasureTheory.Lp.memLp f)
        ((Complex.measurable_ofReal.comp hc).aestronglyMeasurable.mul
          (MeasureTheory.Lp.aestronglyMeasurable f))
        (Filter.Eventually.of_forall fun x => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg _) (hb x)) :
        MeasureTheory.MemLp (fun x : X => (c x : ℂ) * f x) 2 ν)
