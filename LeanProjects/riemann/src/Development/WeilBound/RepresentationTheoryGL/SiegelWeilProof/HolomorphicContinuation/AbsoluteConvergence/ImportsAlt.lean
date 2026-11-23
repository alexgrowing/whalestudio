import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightAlt

noncomputable section

open MeasureTheory Set Filter Topology GlobalTheory.Cont

namespace PositivityTheory.Rg.Sw.AbsSt

private theorem ev_ne_lemma {f : ℂ → ℂ} (hf : Differentiable ℂ f) (ha : ∃ a, f a ≠ 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
  rcases (hf.analyticAt z).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    obtain ⟨a, ha⟩ := ha
    have hon : AnalyticOnNhd ℂ f univ := fun x _ => hf.analyticAt x
    exact ha (hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z) h (mem_univ a))
  · exact h

end PositivityTheory.Rg.Sw.AbsSt
