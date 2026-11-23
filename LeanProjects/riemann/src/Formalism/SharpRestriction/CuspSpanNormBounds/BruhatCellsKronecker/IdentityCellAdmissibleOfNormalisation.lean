import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdentityCellAdmissibleOfLift
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLift

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

section Rec

variable {D : D7}

theorem cIdFlag_of_tie (X : TermTie D)
    (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1) : UnitaryVolumeMass.cIdFlag D X :=
  cIdFlag_of_lift X (id_lift D) hTg

end Rec

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))

end Formalism.MainNotions.BridgeLemma

end
