import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionComparisonAdmissibleEveryPlaceOver
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_comparison_admissible_every_place_over : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i := by
  first | exact @GlobalTheory.BridgeTie.localCoefficientCompatibility | exact GlobalTheory.BridgeTie.localCoefficientCompatibility | (intros; apply GlobalTheory.BridgeTie.localCoefficientCompatibility <;> assumption)
