import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopSeparation
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_separation : GlobalTheory.FunPr.Hypotheses₂ → TopSep := by
  first | exact @GlobalTheory.SepRows.SepProof.topSep_of_classicalTheorems | exact GlobalTheory.SepRows.SepProof.topSep_of_classicalTheorems | (intros; apply GlobalTheory.SepRows.SepProof.topSep_of_classicalTheorems <;> assumption)
