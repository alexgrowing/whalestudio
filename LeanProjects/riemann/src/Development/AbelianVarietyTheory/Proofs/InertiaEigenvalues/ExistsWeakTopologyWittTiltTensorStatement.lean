import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weak_topology_witt_tilt_tensor : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ Continuous (fun p : ↥(GK K) × TW (RW LL) T => TWact (AI.gRW LL (p.1 : GQ l)) T p.1 p.2) ∧ Topology.IsEmbedding (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ CompactSpace ↥T.L.T ∧ ∀ U ∈ nhds (0 : ↥T.L.T), ∃ k : ℕ, ∀ t : ↥T.L.T, l ^ k • t ∈ U := by
  first | exact @GlobalTheory.WeakTop.exists_weakTop | exact GlobalTheory.WeakTop.exists_weakTop | (intros; apply GlobalTheory.WeakTop.exists_weakTop <;> assumption)
