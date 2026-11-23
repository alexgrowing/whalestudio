import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultiplicationFunction
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultiplicationNormBound

theorem UpperTheory.Reformulated.B.MulLinearAe.mulL_ae.{u_1} :
    ∀ {X : Type u_1} [inst : MeasurableSpace X] {ν : MeasureTheory.Measure X} (c : X → ℝ) (hc : Measurable c)
      (hb : ∀ (x : X), |c x| ≤ (1 : ℝ)) (f : ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν)),
      (↑(↑((UpperTheory.Reformulated.B.MultiplicationNormBound.mulL c hc hb : ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν) → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν))
                        f) :
              X →ₘ[ν] ℂ) :
          X → ℂ) =ᵐ[ν]
        fun (x : X) ↦ (↑(c x) : ℂ) * (↑(↑f : X →ₘ[ν] ℂ) : X → ℂ) x := by
  intro X _ ν c hc hb f
  have h : MeasureTheory.MemLp (fun x : X => (c x : ℂ) * f x) 2 ν :=
    (MeasureTheory.Lp.memLp f).of_le
      ((Complex.measurable_ofReal.comp hc).aestronglyMeasurable.mul
        (MeasureTheory.Lp.aestronglyMeasurable f))
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hb x))
  exact h.coeFn_toLp
