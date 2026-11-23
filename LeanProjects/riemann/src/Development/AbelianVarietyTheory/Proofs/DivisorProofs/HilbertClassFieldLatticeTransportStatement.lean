import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertClassFieldLatticeTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_class_field_lattice_transport : GlobalTheory.Published.HilbertClassFieldJ → LatAlg → LatConj → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport := by
  first | exact @GlobalTheory.TransportProof.transport_of | exact GlobalTheory.TransportProof.transport_of | (intros; apply GlobalTheory.TransportProof.transport_of <;> assumption)
