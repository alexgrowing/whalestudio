import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermWeierstrassDivision
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermWeierstrassPreparation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StWeierstrassPolynomialDivision
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

theorem WeierstrassDivision.proof (hP : WeierstrassPreparation.Statement)
    (hD : WeierstrassPolynomialDivision.Statement) : WeierstrassDivision.Statement := by
  intro σ _ d f g hf hg hord
  obtain ⟨e, c, he, he0, hc, hc0, hfe⟩ := hP σ d f hf hord
  obtain ⟨q, a, hq, ha, hgq⟩ := hD σ d c g hc hc0 hg
  refine ⟨fun x => q x / e x, a, hq.div he he0, ha, ?_⟩
  filter_upwards [hfe, hgq, he.continuousAt.eventually_ne he0] with x hfx hgx hex
  rw [hgx, hfx, div_mul_eq_mul_div, mul_left_comm, mul_div_cancel_left₀ _ hex]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
