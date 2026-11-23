import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTateH2Top
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_tate_H2_top : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.admH2 i := by
  first | exact @GlobalTheory.IntTateTop.admH2_of_duality | exact GlobalTheory.IntTateTop.admH2_of_duality | (intros; apply GlobalTheory.IntTateTop.admH2_of_duality <;> assumption)
