import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPeriodGivesBesselPeriodOfLift
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_period_gives_bessel_period_of_lift : ∀ D : D7, UpBF D := by
  first | exact @GlobalTheory.UpBessel.upBF | exact GlobalTheory.UpBessel.upBF | (intros; apply GlobalTheory.UpBessel.upBF <;> assumption)
