import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsKB

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

theorem rows_RowsF_of_one (hAdm : VanishingOnXAndXPlus.AdmF Fm C1 X Y) (hAmp : rows_AmpF Fm C1) (hT : rows_TiesF Fm C1 X Y)
    (hOne : rows_OneF Fm C1 X Y) : RowsF Fm C1 X Y :=
  rows_RowsF_of Fm C1 X Y (rows_NDF_of Fm C1 X Y hAdm hAmp hT) (rows_DegF_of' Fm C1 X Y hAdm hAmp hT) hOne

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
