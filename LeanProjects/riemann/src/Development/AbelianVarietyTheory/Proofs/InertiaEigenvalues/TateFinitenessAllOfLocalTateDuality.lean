import Mathlib
import Formalism.AdmissibleDesigns.RestrictedSevenEightOfFull
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1PeriodDatumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntegersFiniteExtGoodCoefficientRingStatement

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory

theorem finAll_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.FinAll D := by
  intro hT D i w hw C
  exact Formalism.MainNotions.LargeLevelLemmas.tate_h1_finite_of_all_coefficients _ _ _
    (GlobalTheory.T.finite_H1_period_datum hT (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw)
    (GlobalTheory.T.padicIntegers_finiteExt_goodCoefficientRing (D.nd.l i) C.LL)

end GlobalTheory
