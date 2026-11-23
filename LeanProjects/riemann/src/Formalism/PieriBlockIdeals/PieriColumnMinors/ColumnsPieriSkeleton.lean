import Formalism.PieriBlockIdeals.LemmaDGradedOfPieriReal
import Formalism.PieriBlockIdeals.PieriColumnMinors.LemmaDSkeletonFour
import Formalism.PieriBlockIdeals.PieriColumnMinors.PieriGenerated

namespace Formalism.CohomologicalDescent.ColumnMinorsFromPieri

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem lemma_d_skeleton_five : LemmaDSkeleton5 := by
  intro O K V P q _ _ _ _ _ _ _ _ _ _ _ S B n w lam2 DelL xi lam l e i' hl hu h1 h2 h3 h4 hsym hpos hfd hdiag hhw h6 h8 h9
  have hF : LP.FormMod S.EW (B.restrict S.W) :=
    { gl := generators_satisfy_gl_relations S
      symm := fun x y => hsym _ _
      pos := fun x hx => hpos _ (fun h => hx (Subtype.ext h))
      adj := fun a b x y => h3 _ _ _ _
      diag := hdiag }
  have h7 := LP.pieri_rule K P S.W q S.EW (B.restrict S.W) lam2 hF hhw n
  have h5 : ∀ v : V, (∀ x : V, B x v = 0) → v = 0 := by
    intro v hv
    by_contra hne
    exact absurd (hv v) (ne_of_gt (hpos v hne))
  exact LC.lemma_d_skeleton_four O K V P q S B n w lam2 DelL xi lam l e i' hl hu h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem columns_real_of_pieri_real : ColumnsRealOfPieriReal := by
  intro hP p q w lam2 hanti hle n tau hcol z hz
  exact Formalism.CohomologicalDescent.LC.columns_from_pieri ℚ (Fin p) _ q _ n lam2 (hP p q w lam2 hanti hle n) tau
    (by simpa using hcol) z hz

end Formalism.CohomologicalDescent.ColumnMinorsFromPieri
