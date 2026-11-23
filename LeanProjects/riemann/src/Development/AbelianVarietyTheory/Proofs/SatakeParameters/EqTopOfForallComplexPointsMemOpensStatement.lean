import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqTopOfForallComplexPointsMemOpens
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_top_of_forall_complexPoints_mem_opens : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens),
    (∀ z : CxPts p (RingHom.id ℂ), z ∈ CxPts.ptsIn p (RingHom.id ℂ) U) → U = ⊤ := by
  first | (exact @GlobalTheory.MaxPt.eq_top_of_forall_cxPts_mem) | (exact GlobalTheory.MaxPt.eq_top_of_forall_cxPts_mem) | (intros; apply GlobalTheory.MaxPt.eq_top_of_forall_cxPts_mem  <;> assumption)
