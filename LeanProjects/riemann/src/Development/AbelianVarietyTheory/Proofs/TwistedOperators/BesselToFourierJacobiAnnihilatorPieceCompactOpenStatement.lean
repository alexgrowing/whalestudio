import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiAnnihilatorPieceCompactOpen
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
theorem _root_.GlobalTheory.T.besselToFourierJacobi_annihilatorPiece_compactOpen : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), IsCompact ((pcBF W F ρ h).A₂ : Set (Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ)) ∧ ∃ U : Set (Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ), IsOpen U ∧ (0 : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ) ∈ U ∧ ∀ a ∈ U, MxAt (fun _ => True) a → a ∈ (pcBF W F ρ h).A₂ := by
  first | exact @GlobalTheory.AnnPiece.pcBF_A₂_compact_open | exact GlobalTheory.AnnPiece.pcBF_A₂_compact_open | (intros; apply GlobalTheory.AnnPiece.pcBF_A₂_compact_open <;> assumption)
