import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardAuxiliaryFramesFitGridEnds
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAuxiliaryFrames_fit_grid_ends : All fun {_} _ _ _ {G} W M => ∀ (v : CoreVol G) (F : Frames G), Std F → F.Ends v W M := by
  first | exact @GlobalTheory.AscFin.EndsPf.ends | exact GlobalTheory.AscFin.EndsPf.ends | (intros; apply GlobalTheory.AscFin.EndsPf.ends <;> assumption)
