import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittTargetProjections
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
theorem _root_.GlobalTheory.T.depthLatticeGridRow_stable_wittTargetProjections : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (_ : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), ((F.dB σ h').jX * (F.dB σ h').pX) * u ∈ latRow G (2 * σ + 2) ∧ ((F.dB σ h').jY * (F.dB σ h').pY) * u ∈ latRow G (2 * σ + 2) := by
  first | exact @GlobalTheory.AscFin.latRow_proj_tgt | exact GlobalTheory.AscFin.latRow_proj_tgt | (intros; apply GlobalTheory.AscFin.latRow_proj_tgt <;> assumption)
