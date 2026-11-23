import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory

theorem linearMap_pi_continuous_coord : ∀ {l : ℕ} [Fact l.Prime] {O M ι : Type} [CommRing O] [Algebra ℤ_[l] O] [Fintype ι] [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] O), (∀ m : M, Continuous fun c : ℤ_[l] => algebraMap ℤ_[l] O c • m) → ∀ f : (ι → O) →ₗ[O] M, letI := TopologicalSpace.induced bO.equivFun inferInstance; Continuous f := by
  intro l _ O M ι _ _ _ _ _ _ _ e bO hcont f
  classical
  letI : TopologicalSpace O := TopologicalSpace.induced bO.equivFun inferInstance
  have key : ∀ c : ι → O, f c = ∑ i, ∑ α, algebraMap ℤ_[l] O (bO.equivFun (c i) α) • (bO α • f (Pi.single i 1)) := by
    intro c
    rw [LinearMap.pi_apply_eq_sum_univ f c]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : (fun j => if i = j then (1:O) else 0) = Pi.single i 1 := by
      funext j; by_cases h : i = j <;> simp [Pi.single_apply, h, eq_comm]
    rw [hc]
    conv_lhs => rw [← bO.sum_equivFun (c i)]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Algebra.smul_def, mul_smul]
  have hf : (f : (ι → O) → M) = fun c => ∑ i, ∑ α, algebraMap ℤ_[l] O (bO.equivFun (c i) α) • (bO α • f (Pi.single i 1)) := funext key
  rw [hf]
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun α _ => ?_
  exact (hcont _).comp ((continuous_apply α).comp (continuous_induced_dom.comp (continuous_apply i)))

end GlobalTheory
