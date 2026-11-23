import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemEtaleTopologyOfPullbackFiniteEtale
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_etaleTopology_of_pullback_finite_etale : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (T : Sieve X), T.pullback f ∈ Scheme.etaleTopology Z → (∀ {V : Scheme.{0}} (v : V ⟶ X), IsEmpty (pullback f v : Scheme.{0}) → T v) → T ∈ Scheme.etaleTopology X := by
  first | (exact @GlobalTheory.EtC.Tr.mem_etaleTopology_of_pullback_finite) | (exact GlobalTheory.EtC.Tr.mem_etaleTopology_of_pullback_finite) | (intros; apply GlobalTheory.EtC.Tr.mem_etaleTopology_of_pullback_finite  <;> assumption)
