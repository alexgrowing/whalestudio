import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalProjectionPreservesDepthLattice
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_projection_preserves_depth_lattice : OnStd fun {D} _ _ _ {G} _ F => ∀ u ∈ latCore G 0, F.oz.jA ⬝ (F.oz.pA ⬝ u) ∈ latCore G 0 := by
  first | exact @GlobalTheory.ProjCore.proj_mem_latCore | exact GlobalTheory.ProjCore.proj_mem_latCore | (intros; apply GlobalTheory.ProjCore.proj_mem_latCore <;> assumption)
