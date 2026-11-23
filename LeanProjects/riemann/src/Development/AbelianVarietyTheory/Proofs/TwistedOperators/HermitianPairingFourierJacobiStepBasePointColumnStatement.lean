import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianPairingFourierJacobiStepBasePointColumn
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MxAtOfMemDepLat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianPairing_fourierJacobi_step_basePoint_columns : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)) (p : Fin (σ + 1)), hA _ (fun k => xFB F σ h' k p) (fun k => a' k p) = hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) := by
  first | exact @GlobalTheory.CharXFB.hA_xFB_col | exact GlobalTheory.CharXFB.hA_xFB_col | (intros; apply GlobalTheory.CharXFB.hA_xFB_col <;> assumption)
