import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointNearCuspScale
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPoint_nearCusp_scale : ∀ I : AutInst, NearInst I := by
  first | exact @GlobalTheory.CuspGeo.nearInst | exact GlobalTheory.CuspGeo.nearInst | (intros; apply GlobalTheory.CuspGeo.nearInst <;> assumption)
