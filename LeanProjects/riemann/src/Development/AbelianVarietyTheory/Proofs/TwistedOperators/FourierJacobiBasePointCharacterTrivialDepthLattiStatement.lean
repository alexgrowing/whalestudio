import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBasePointCharacterTrivialDepthLatti
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
theorem _root_.GlobalTheory.T.fourierJacobi_basePoint_character_trivial_depthLattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)), (F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' ∈ latRow G (2 * σ + 2) → W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (xFB F σ h')) ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a')) = 1 := by
  first | exact @GlobalTheory.CharXFB.charx_fb | exact GlobalTheory.CharXFB.charx_fb | (intros; apply GlobalTheory.CharXFB.charx_fb <;> assumption)
