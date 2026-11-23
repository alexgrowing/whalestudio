import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRedMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepVec

theorem omegaQ_one_eq_prod_qLoc : ∀ (D : D7) (a b r : ℕ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)),
      omegaQ Q r ξ 1 y = ∏ PP ∈ Q, qLoc r PP (ξ PP) (y PP) := by
  intro D a b r Q ξ y
  unfold omegaQ
  by_cases h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
  · rw [dif_pos h, ← Finset.prod_attach Q (fun PP => qLoc r PP (ξ PP) (y PP))]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [zpow_one, qLoc, dif_pos (h PP.1 PP.2)]
  · rw [dif_neg h]
    push_neg at h
    obtain ⟨PP, hPP, hn⟩ := h
    refine (Finset.prod_eq_zero hPP ?_).symm
    rw [qLoc, dif_neg]
    rintro ⟨h1, h2⟩
    exact hn h1 h2

end GlobalTheory.StepVec
