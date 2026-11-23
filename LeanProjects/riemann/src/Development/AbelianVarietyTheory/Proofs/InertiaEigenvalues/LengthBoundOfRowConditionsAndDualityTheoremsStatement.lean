import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthBoundOfRowConditionsAndDualityTheorems
import Formalism.AdmissibleDesigns.RestrictedSevenEightOfFull
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lengthBound_of_rowConditions_and_dualityTheorems : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.AllDesignConditions D → TruncatedSeriesCountingIdentities.Stmt D := by
  first | exact @GlobalTheory.InertiaEigenvalues.LengthBoundClosing.stmt_closed | exact GlobalTheory.InertiaEigenvalues.LengthBoundClosing.stmt_closed | (intros; apply GlobalTheory.InertiaEigenvalues.LengthBoundClosing.stmt_closed <;> assumption)
