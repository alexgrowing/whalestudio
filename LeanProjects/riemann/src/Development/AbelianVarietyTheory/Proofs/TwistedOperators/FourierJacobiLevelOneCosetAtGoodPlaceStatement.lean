import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiLevelOneCosetAtGoodPlace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiLevel_oneCoset_at_goodPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ A L : HSp D) (σ : ℕ) (dV : HypDec V V₀ (σ + 1)) (dW : HypDec W W₀ σ) (o : OrthDec W₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (p : Pieces V₀ W W₀ (σ + 1) σ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (LA : Lat A) (LL : Lat L) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xLast dW (vecB o ζ)) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → IsSelfDualC A LA → IsSelfDualC L LL → OrthAt o LW₀ LA LL v → ∀ h ∈ grpAt W (· = v), Cond dW p (xLast dW (vecB o ζ)) 0 ψ (· = v) h → CosetAt W (Rgrp W (xLast dW (vecB o ζ))) LW v h := by
  first | exact @GlobalTheory.AscFin.OneCosetFJ.oneCoset_good | exact GlobalTheory.AscFin.OneCosetFJ.oneCoset_good | (intros; apply GlobalTheory.AscFin.OneCosetFJ.oneCoset_good <;> assumption)
