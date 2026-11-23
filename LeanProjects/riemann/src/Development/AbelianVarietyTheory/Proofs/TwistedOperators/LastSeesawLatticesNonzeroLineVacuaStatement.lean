import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLatticesNonzeroLineVacua
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_seesaw_lattices_nonzero_line_vacua : OnStd fun {D} _ _ _ {G} W F => (∀ ρ, 2 * ρ + 2 ≤ D.R.m → ∃ Φ₀, VacG W.ψ _ _ (lineLat F ρ) Φ₀ ∧ Φ₀ ≠ 0) ∧ ∀ (v : CoreVol G) h, LastLat W.ψ (F.jac v 0 h) F.oz (latRow G 0) (lineLat F 0) (latCore G 0) := by
  first | exact @GlobalTheory.LastSeeSaw.lastLat_std | exact GlobalTheory.LastSeeSaw.lastLat_std | (intros; apply GlobalTheory.LastSeeSaw.lastLat_std <;> assumption)
