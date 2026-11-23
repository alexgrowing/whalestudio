import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicSaturatedSubmoduleOfFinrankLe
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropicSaturatedSubmodule_of_finrank_le : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (r : ℕ), r ≤ min D.p D.q →
    ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = r := by
  first | exact @GlobalTheory.LowFilt.exists_isIsoSat_finrank | exact GlobalTheory.LowFilt.exists_isIsoSat_finrank | (intros; apply GlobalTheory.LowFilt.exists_isIsoSat_finrank <;> assumption)
