import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeIsotropicPair
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oppositeIsotropicPair : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (Z : Submodule (𝓞 E) D.La), IsIsoSat D Z → ∃ Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' := by
  first | exact @GlobalTheory.LowFilt.Opp.exists_opp | exact GlobalTheory.LowFilt.Opp.exists_opp | (intros; apply GlobalTheory.LowFilt.Opp.exists_opp <;> assumption)
