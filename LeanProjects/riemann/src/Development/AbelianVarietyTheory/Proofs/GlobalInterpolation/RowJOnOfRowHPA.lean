import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ClassCountBoundAtConstructedPoints
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowJOnOfRealisations

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.JOnBundle

theorem row_jOn_of_row_hPA : ∀ (Q : V4.Slot) (Lk : LkT Bundle), R1.PeriodAdmissibilityAtBundlePoints Q Lk → R0.JInvariantConditionAtConstructedPoints Q Lk := by
  intro Q Lk h
  apply GlobalTheory.JOnRow.row_jOn_of_realisations Bundle Q Lk
  refine Row.imp h fun 𝒜 σ _ hA => ?_
  intro eps Fm hc x hx i
  have hb := hA Fm hc x hx i
  exact ⟨(σ Fm hc x hx i).R, (σ Fm hc x hx i).P, _, _, _, (σ Fm hc x hx i).S, _, inferInstance, inferInstance, inferInstance,
    (σ Fm hc x hx i).B.Q, 1, (σ Fm hc x hx i).C.ok1, hb.2, hb.1⟩

end GlobalTheory.Fc.JOnBundle

end
