import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateFinitenessAllOfLocalTateDuality
import Formalism.AdmissibleDesigns.RestrictedSevenEightOfFull
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateFinitenessAll_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.FinAll D := by
  first | exact @GlobalTheory.finAll_of_localTateDuality | exact GlobalTheory.finAll_of_localTateDuality | (intros; apply GlobalTheory.finAll_of_localTateDuality <;> assumption)
