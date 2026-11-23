import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf

open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

theorem nonzero : NonZero := by
  intro X S _ ν _ F f hF hf h0
  have hmeas : MeasurableSet {p : X.G × S | f p.1 p.2 = 0} :=
    (measurableSet_singleton (0 : ℂ)).preimage hf.1
  have h1 : ∀ᵐ x ∂X.μ, ∀ᵐ s ∂ν, f x s = 0 :=
    (Measure.ae_ae_comm (μ := X.μ) (ν := ν) (p := fun x s => f x s = 0) hmeas).2 h0
  have h2 : F =ᵐ[X.μ] (0 : X.G → Lp ℂ 2 ν) := by
    filter_upwards [h1] with x hx
    have : (F x : S → ℂ) =ᵐ[ν] 0 := by
      filter_upwards [(hf.2 x).symm, hx, Lp.coeFn_zero ℂ 2 ν] with s h1 h2 h3
      rw [h1, h2]; rfl
    simpa using (Lp.eq_zero_iff_ae_eq_zero).2 this
  exact (Continuous.ae_eq_iff_eq X.μ hF continuous_const).1 h2

end PositivityTheory.Rg.BcB.E2.P
