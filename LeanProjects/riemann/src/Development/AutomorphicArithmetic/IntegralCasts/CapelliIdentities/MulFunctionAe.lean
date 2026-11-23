import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultiplicationFunction

theorem UpperTheory.Reformulated.B.MulFunctionAe.mulFn_ae.{u_1} :
    ∀ {X : Type u_1} [inst : MeasurableSpace X] {ν : MeasureTheory.Measure X} (c : X → ℝ) (hc : Measurable c)
      (hb : ∀ (x : X), |c x| ≤ (1 : ℝ)) (f : ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν)),
      (↑(↑(UpperTheory.Reformulated.B.MultiplicationFunction.mulFn c hc hb f) : X →ₘ[ν] ℂ) : X → ℂ) =ᵐ[ν] fun (x : X) ↦
        (↑(c x) : ℂ) * (↑(↑f : X →ₘ[ν] ℂ) : X → ℂ) x := by
  intro X inst ν c hc hb f
  unfold UpperTheory.Reformulated.B.MultiplicationFunction.mulFn
  exact MeasureTheory.MemLp.coeFn_toLp _
