import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockEqSum
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFCoarse
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SymbolFormOfOrthogonality
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BlockForm

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

theorem symbol_form_of_block_parts {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) (hK : RestKapNum) (hO : RestOPlus) : RestForm :=
  symbol_form_of_orthogonality (restBlockForm_of h52 hK) orthAt hO

theorem restKapNum_of {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) (hO : RestOPlus) : RestKapNum := by
  unfold RestKapNum TransportedAlt
  unfold RestOPlus TransportedAlt at hO
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := hO Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 Cm hE1 hE2 hCm => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 Cm hE1 hE2 hCm
  refine ⟨T2, hT2, fun CYb Cde Ck CD Cb ha hb hc hd he => ?_⟩
  have hOP := h2 CYb Cde Ck CD Cb ha hb hc hd he
  exact kapNumAt_of h52 (trueDegAt_of hOP) (coarseMultAt_of hOP)

theorem restForm_of_oplus {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) (hO : RestOPlus) : RestForm :=
  symbol_form_of_block_parts h52 (restKapNum_of h52 hO) hO

end Formalism.MainNotions.ColumnSystems.Pf
