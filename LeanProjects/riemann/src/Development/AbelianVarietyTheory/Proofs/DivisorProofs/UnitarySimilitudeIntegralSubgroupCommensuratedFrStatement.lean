import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFr
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySimilitudeIntegralSubgroup_commensurated_frobenius : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → (∀ g : Gr G r, Subgroup.Commensurable ((KHT p G.m G.n r G.Fw).map (MulAut.conj g).toMonoidHom) (KHT p G.m G.n r G.Fw)) ∧ (KHT p G.m G.n r G.Fw).comap (inclG G r) = Kp0 G ∧ (KHT p G.m G.n r G.Fw).map (sigG G r) ≤ KHT p G.m G.n r G.Fw := by
  first | (exact @GlobalTheory.heckeOperator_integral) | (exact GlobalTheory.heckeOperator_integral) | (intros; apply GlobalTheory.heckeOperator_integral  <;> assumption)
