import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledLatticeCompletionSupportedInvIdealSmul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledLatticeCompletion_supported_invIdeal_smul : ∀ {D : D7} (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (I : GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D) (y : Fin S.rank → AE D), y ∈ GlobalTheory.FinPl.latMul S {a | a ∈ I} L (· = v) → (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ GlobalTheory.SeeSaw.idV I⁻¹ v, s • y ∈ latV S L (· = v) := by
  first | exact @GlobalTheory.LatMulAt.latMul_inv_smul | exact GlobalTheory.LatMulAt.latMul_inv_smul | (intros; apply GlobalTheory.LatMulAt.latMul_inv_smul <;> assumption)
