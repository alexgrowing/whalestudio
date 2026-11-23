import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsIrrDistinctMapSurjective
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrDistinct_map_surjective : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L), Function.Surjective f → ∀ {a : ℕ} (M : Γ →* Matrix (Fin a) (Fin a) k), AbsIrrDistinct (matRep M) → AbsIrrDistinct (matRep (mapM f M)) := by
  first | exact @GlobalTheory.absIrrDistinct_matRep_mapM_of_surjective | exact GlobalTheory.absIrrDistinct_matRep_mapM_of_surjective | (intros; apply GlobalTheory.absIrrDistinct_matRep_mapM_of_surjective <;> assumption)
