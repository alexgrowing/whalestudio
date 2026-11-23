import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepDiagonalCoordinatesMemComplementIdeal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulMemComplId
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselStep_diagonalCoordinates_mem_complementIdeal : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : Frames G}, Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (u : WO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))), u ∈ latO _ _ (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) → ∀ p : Fin ρ, ((F.dJ ρ h).pY ⬝ u ⬝ (F.dB ρ h).jY) p p ∈ complId (D.host.AA * G.pl.stAbar sc) := by
  first | exact @GlobalTheory.XCharBF.DiagCoord.diag_mem_complId | exact GlobalTheory.XCharBF.DiagCoord.diag_mem_complId | (intros; apply GlobalTheory.XCharBF.DiagCoord.diag_mem_complId <;> assumption)
