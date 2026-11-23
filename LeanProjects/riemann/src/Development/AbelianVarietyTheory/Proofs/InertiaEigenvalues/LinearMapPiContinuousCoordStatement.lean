import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearMapPiContinuousCoord
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_linearMap_pi_of_continuous_coord : ∀ {l : ℕ} [Fact l.Prime] {O M ι : Type} [CommRing O] [Algebra ℤ_[l] O] [Fintype ι] [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] O), (∀ m : M, Continuous fun c : ℤ_[l] => algebraMap ℤ_[l] O c • m) → ∀ f : (ι → O) →ₗ[O] M, letI := TopologicalSpace.induced bO.equivFun inferInstance; Continuous f := by
  first | exact @GlobalTheory.linearMap_pi_continuous_coord | exact GlobalTheory.linearMap_pi_continuous_coord | (intros; apply GlobalTheory.linearMap_pi_continuous_coord <;> assumption)
