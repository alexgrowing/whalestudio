import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselPiecesMutualAnnihilators
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_to_bessel_pieces_mutual_annihilators : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), (∀ ξ, MxAt (fun _ => True) ξ → (ξ ∈ (pcFB W F σ h h').B₁ ↔ ∀ η ∈ (pcFB W F σ h h').B₂, W.ψ (symplO _ _ ((F.dB σ h').incX _ ξ) ((F.dB σ h').incY _ η)) = 1)) ∧ (∀ η, MxAt (fun _ => True) η → (η ∈ (pcFB W F σ h h').B₂ ↔ ∀ ξ ∈ (pcFB W F σ h h').B₁, W.ψ (symplO _ _ ((F.dB σ h').incX _ ξ) ((F.dB σ h').incY _ η)) = 1)) := by
  first | exact @GlobalTheory.AscFin.DualParts.pcFB_dual | exact GlobalTheory.AscFin.DualParts.pcFB_dual | (intros; apply GlobalTheory.AscFin.DualParts.pcFB_dual <;> assumption)
