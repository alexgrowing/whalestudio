import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeStabilizerAtPlaceMemDepthCongruenceGridNo
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabilizerAtPlace_mem_depthCongruence_gridNode : All fun {D} _ _ _ {G} _ _ => ∀ i, i ≤ D.R.m → ∀ v, v ∉ G.pl.S0 → ∀ κ, InK (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) κ → κ ∈ lev G (.grid i 0) := by
  first | exact @GlobalTheory.LevelOffS.inK_mem_lev | exact GlobalTheory.LevelOffS.inK_mem_lev | (intros; apply GlobalTheory.LevelOffS.inK_mem_lev <;> assumption)
