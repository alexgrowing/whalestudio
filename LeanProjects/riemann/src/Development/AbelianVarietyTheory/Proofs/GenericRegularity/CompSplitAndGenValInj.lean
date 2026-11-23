import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspRestrictComp
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.Reg

theorem compSplit_and_genValInj : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), ∀ hG : GenFrEx (T.Q.Xo j) T.Q.c, CompSplitSt h j hG ∧ GenValInjSt h j hG := by
  intro D T h j hj hG
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c
  refine ⟨fun Z w g => ?_, fun w g h0 => ?_⟩
  · have hg := cutR_le T.C j w g.2
    obtain ⟨g', hg', h1, h2⟩ := exists_cusp_restrict_comp _ _ _ _ (T.Q.Xo j) T.Q.c hL hG (hA hG) D.R.r
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (fun σ hσ => h.unf j hj σ hσ) Z (wtA w) w.n _ hg
    have hm : g' ∈ cutR T.C j w := by
      rw [cutR_eq T.C hj]; exact hg'
    exact ⟨⟨g', hm⟩, h1, h2⟩
  · exact Subtype.ext (sec_eq_zero_of_generic_values _ _ _ _ (T.Q.Xo j) T.Q.c hL hG (hA hG) (wtA w) w.n _
      (cusp_le_sec _ _ _ _ _ (cutR_le T.C j w g.2)) h0)

end GlobalTheory.Reg
