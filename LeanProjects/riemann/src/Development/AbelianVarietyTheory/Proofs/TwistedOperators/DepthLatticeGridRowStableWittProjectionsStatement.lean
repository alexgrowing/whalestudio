import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittProjections
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeGridRow_stable_witt_projections : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (_ : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), u * ((F.dJ (σ + 1) h).jX * (F.dJ (σ + 1) h).pX) ∈ latRow G (2 * σ + 2) ∧ u * ((F.dJ (σ + 1) h).jY * (F.dJ (σ + 1) h).pY) ∈ latRow G (2 * σ + 2) := by
  first | exact @GlobalTheory.ProjLat.latRow_proj | exact GlobalTheory.ProjLat.latRow_proj | (intros; apply GlobalTheory.ProjLat.latRow_proj <;> assumption)
