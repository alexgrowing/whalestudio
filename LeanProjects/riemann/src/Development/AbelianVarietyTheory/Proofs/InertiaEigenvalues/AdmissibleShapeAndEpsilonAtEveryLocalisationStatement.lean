import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleShapeAndEpsilonAtEveryLocalisation
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_shape_and_epsilon_at_every_localisation : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.CyclotomicCompletionAdmissible (D := D) i ∧ TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i := by
  first | exact @GlobalTheory.admissible_shape_and_epsilon_at_every_localisation.main | exact GlobalTheory.admissible_shape_and_epsilon_at_every_localisation.main | (intros; apply GlobalTheory.admissible_shape_and_epsilon_at_every_localisation.main <;> assumption)
