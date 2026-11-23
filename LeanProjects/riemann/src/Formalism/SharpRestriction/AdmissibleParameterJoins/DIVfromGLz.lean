import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLe
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Formalism.SharpRestriction.GlobalSchurBounds.JointsL
import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions NumberField

theorem level_prime_splits_totally_real (D : D7) (u : D.what₂.Word) : StandardLattice.SplitsF D (D.mem u).A.T := by
  have : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have h := Formalism.BasicNotions.Examples₂.placesOver_ncard_of_split D.host (D.mem u).A.T (D.T_mod_cond u)
  have h' := splits_sub D.host.F (D.mem u).A.T D.host.E (D.mem u).A.T_prime h
  rw [finrank_F_eq] at h'
  exact h'

end Formalism.MainNotions.J

end
