import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFibreSteps
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

theorem FrameSpanTop.proof : FrameSpanTop.Statement := by
  intro K _ ι _ Ω _ E _ _ N y W c f b hb
  obtain ⟨h0, -, -, hli, -⟩ := hb
  obtain ⟨k, f', c', -, -, hsum, hfr⟩ := W.frame c h0
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hsum
    · exact hk
  obtain ⟨b0, hli0, hsp0, -⟩ := hfr ⟨0, hk⟩
  let B : Module.Basis (Fin N) Ω E := Module.Basis.mk hli0 hsp0.ge
  have : FiniteDimensional Ω E := Module.Basis.finiteDimensional_of_finite B
  have hrank : Module.finrank Ω E = N := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  exact hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hrank])

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
