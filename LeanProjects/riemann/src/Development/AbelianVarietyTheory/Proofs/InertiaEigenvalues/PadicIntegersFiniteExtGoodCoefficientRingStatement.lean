import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntegersFiniteExtGoodCoefficientRing
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicIntegers_finiteExt_goodCoefficientRing : LitGoodO := by
  first | exact @GlobalTheory.LitGood.litGoodO | exact GlobalTheory.LitGood.litGoodO | (intros; apply GlobalTheory.LitGood.litGoodO <;> assumption)
