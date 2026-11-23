import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingSieveMemEtaleTopology
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoveringOfForallMem
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splittingSieve_mem_etaleTopology : ∀ {Z X S : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (x : S ⟶ X), GlobalTheory.EtC.Tr.splitSieve f x ∈ Scheme.etaleTopology S := by
  first | exact @GlobalTheory.EtC.Tr.splitSieve_mem | exact GlobalTheory.EtC.Tr.splitSieve_mem | (intros; apply GlobalTheory.EtC.Tr.splitSieve_mem <;> assumption)
