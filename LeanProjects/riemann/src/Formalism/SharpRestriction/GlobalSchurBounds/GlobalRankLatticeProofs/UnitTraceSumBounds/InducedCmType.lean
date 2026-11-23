import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem induced_cm_type (D : D7) : InducedCMType D := by
  intro τ a

  have hmem : embT D τ ∈ Formalism.MainNotions.GlobalTheoryTheory.PhiEmb D := ⟨((D.eTau τ : D.R.Psi) : D.R.GG), (D.eTau τ).2, rfl⟩
  exact (Formalism.MainNotions.UnusedSlot33.second_proposition_every_localisation D).2.1 _ hmem _ a.2

theorem cm_field_facts_hold (D : D7) : HostFieldConditions D :=
  Formalism.MainNotions.TaylorLogMetric.first_hypothesis_of_lifting D (Formalism.MainNotions.UnusedSlot33.ramification_two_and_conjugation_at_q_and_d D)

end Formalism.MainNotions.GL3Theta
