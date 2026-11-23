import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantTraceGeneratorLocal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_invariant_trace_generator_local : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (𝔭 : Ideal (𝓞 E))
    (h𝔭 : 𝔭.IsMaximal),
    ∃ θ : 𝓞 E →+ ℤ, (∀ t, θ (H.bar t) = θ t) ∧ ∃ s : 𝓞 E, s ∉ 𝔭 ∧ H.bar s ∉ 𝔭 ∧
      ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u) := by
  first | exact @GlobalTheory.RealTheta.exists_bar_inv_trace_gen | exact GlobalTheory.RealTheta.exists_bar_inv_trace_gen | (intros; apply GlobalTheory.RealTheta.exists_bar_inv_trace_gen <;> assumption)
