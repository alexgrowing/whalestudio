import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedHomsBoundedByClassNumberOfArtin
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedClassFieldBound_of_artin : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.UnramifiedClassFieldBound i := by
  first | exact @GlobalTheory.UnramifiedHomBound.unramified_homs_bounded_by_class_number_of_artin | exact GlobalTheory.UnramifiedHomBound.unramified_homs_bounded_by_class_number_of_artin | (intros; apply GlobalTheory.UnramifiedHomBound.unramified_homs_bounded_by_class_number_of_artin <;> assumption)
