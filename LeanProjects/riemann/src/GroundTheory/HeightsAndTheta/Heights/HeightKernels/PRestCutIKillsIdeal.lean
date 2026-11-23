import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem rootPsum_isHomogeneous (f j k m : ℕ) (τ : Fin f) :
    (rootPsum f j k m τ).IsHomogeneous m :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_X_pow _ _

theorem restTransport_isHomogeneous (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k)
    {A : RestTerms.RootRing f N} {d : ℕ} (hA : A.IsHomogeneous d) :
    (restTransport f j k N e A).IsHomogeneous d := by
  show (rename (fun p : Fin f × Fin N => (p.1, e p.2)) (map (algebraMap ℚ ℝ) A)).IsHomogeneous d
  exact (hA.map _).rename_isHomogeneous

theorem RestCutIKillsIdeal.proof (h₁ : RestCutIdealSum.Statement)
    (h₂ : RestCutTransportPsum.Statement) : RestCutIKillsIdeal.Statement := by
  intro f j k N e I hI A hA hhom
  obtain ⟨G, hG⟩ := h₁ f N A hA
  have hT := restTransport_isHomogeneous f j k N e hhom
  have hC := homogeneousComponent_of_mem (m := flagDim f j k) hT
  rw [if_pos rfl] at hC
  rw [← hC]
  rw [hG, map_sum, map_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_mul, h₂, KRest.homogeneousComponent_mul_left (rootPsum_isHomogeneous f j k _ i.2)]
  split_ifs with hle
  · exact hI.kills _ _ _ (Nat.succ_le_succ (Nat.zero_le _)) hle
      (homogeneousComponent_isHomogeneous _ _)
  · exact map_zero I

end GroundTheory.Heights₂.Heights
