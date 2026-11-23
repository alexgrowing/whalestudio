import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolC

noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW PositiveNearLattice SdDualW VolAAW

theorem volAA_of (hC : CondAA) : VolAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  filter_upwards [hC F ψ hψ, ev_dual b σ hσ J hJ.2 (a := a), ev_dualH b σ hσ a] with v hCv hDW hDH
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  refine ⟨fun μv hμ => ?_, fun νv hν => ?_⟩
  · have hA := ann_eq v (psiV F ψ v) (BR (Fv F v) σ J (n := a)) (latV (M := M) (n := a) b v) hCv
      (smul_latV b v σ J) hDW
    exact vol_one_of_ann hμ (fun X T Y => by rw [BR_add, psiV_add]) (SdDualW.latSub v b a M)
      (isCompact_latV b v a M) (isClopen_latV b v a M).isOpen hA
  · have hA := ann_eq v (psiV F ψ v) (pairHerm (Fv F v) σ a)
      (hermO b v σ a : Set (HermR (Fv F v) σ a)) hCv (smul_hermO b v σ a) hDH
    exact vol_one_of_ann hν (fun S T U => by rw [pairHerm_add, psiV_add]) (hermO b v σ a)
      (isCompact_hermO b v σ a).1 (isCompact_hermO b v σ a).2 hA

end PI.VolStabSW
