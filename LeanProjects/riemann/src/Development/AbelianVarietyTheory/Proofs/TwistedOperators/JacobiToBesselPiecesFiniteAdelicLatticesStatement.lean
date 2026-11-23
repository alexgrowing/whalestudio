import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselPiecesFiniteAdelicLattices
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_to_bessel_pieces_finite_adelic_lattices : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), FinLat (pcFB W F σ h h').A₁ ∧ FinLat (pcFB W F σ h h').B₁ ∧ FinLat (pcFB W F σ h h').B₂ ∧ ∀ u ∈ (pcFB W F σ h h').Γ₀, MxAt (fun _ => True) u := by
  first | exact @GlobalTheory.AscFin.pcFB_fin | exact GlobalTheory.AscFin.pcFB_fin | (intros; apply GlobalTheory.AscFin.pcFB_fin <;> assumption)
