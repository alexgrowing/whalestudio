import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.PlaneGramTheoremOfLemmas
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SecondValuationOfAdmitted
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrRenExpandMonomial
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.UnitLevelOne
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrSpan

noncomputable section

namespace Formalism.MainNotions.PlaneGram

open Formalism.MainNotions.G

theorem stmt (D : Formalism.BasicNotions.D7) {CH : ℝ} (hCH : 26 ≤ CH) : Formalism.MainNotions.PlaneGramData.Stmt D CH 2 24 60 := by
  intro p O _ _ _ _ hSet hAdm
  obtain ⟨⟨S⟩, n', hG⟩ := hSet
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := hAdm
  exact Br.plane_gram_of_theorem_at S hG
    (plane_gram_theorem_of_five_lemmas le_rfl (second_valuation_of_admitted h2) (brSPAN S h3) (brPROJ S h4) (brDIG D S hG h5)
      (brDER S h6)) hCH

theorem stmtE (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.PlaneGramData.ClosedFormOfAdmitted D :=
  ⟨26, 2, 24, 60, by norm_num, by norm_num, by norm_num, by norm_num, fun _ hCH => stmt D hCH⟩

theorem stmtEF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Formalism.MainNotions.PlaneGramData.FamilyClosedForm Fm :=
  ⟨26, 2, 24, 60, by norm_num, by norm_num, by norm_num, by norm_num, 0, fun _ hCH _ _ _ => stmt _ hCH⟩

theorem stmtEDF (Fm : Formalism.MainNotions.DFamP) : Formalism.MainNotions.PlaneGramData.DerivativeStatementClosedDesign Fm :=
  ⟨26, 2, 24, 60, by norm_num, by norm_num, by norm_num, by norm_num,
    fun _ _ _ => ⟨0, fun _ hCH _ _ _ => stmt _ hCH⟩⟩

end Formalism.MainNotions.PlaneGram
