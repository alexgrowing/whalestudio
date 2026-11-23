import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroFractionRingCoefficientRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charZero_fractionRing_coefficientRing : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw), CharZero (FractionRing (T.O i)) := by
  first | exact @GlobalTheory.HeightCounting.TwR.charZero_fractionRing_O | exact GlobalTheory.HeightCounting.TwR.charZero_fractionRing_O | (intros; apply GlobalTheory.HeightCounting.TwR.charZero_fractionRing_O <;> assumption)
