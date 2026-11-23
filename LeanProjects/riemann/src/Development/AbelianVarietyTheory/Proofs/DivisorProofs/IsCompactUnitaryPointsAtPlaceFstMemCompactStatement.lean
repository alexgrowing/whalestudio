import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryPointsAtPlaceFstMemCompact
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_unitaryPointsAtPlace_fst_mem_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C); ∀ K : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact K → IsCompact {d : Gv G v | (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ K} := by
  first | (exact @GlobalTheory.OrbFinAf.isCompact_setOf_fst_mem) | (exact GlobalTheory.OrbFinAf.isCompact_setOf_fst_mem) | (intros; apply GlobalTheory.OrbFinAf.isCompact_setOf_fst_mem  <;> assumption)
