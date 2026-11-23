import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLevelElementOffPlace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_element_off_place : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * σ + 2) 0)) (· = v), ∀ (u : UX D (σ + 1)), ∀ a ∈ (pcFB W F σ h h').A₁, MxOff (· = v) (mt (G.V (.grid (2 * σ + 2) 0)) g⁻¹ ⬝ (xFB F σ h' ⬝ u.1.1) - xFB F σ h' - a) → ∃ k ∈ lev G (.grid (2 * σ + 2) 0), k ∈ grpAt (G.V (.grid (2 * σ + 2) 0)) (· = v) ∧ MxOff (· = v) (mt (G.V (.grid (2 * σ + 2) 0)) k ⬝ xFB F σ h' - mt (G.V (.grid (2 * σ + 2) 0)) g⁻¹ ⬝ (xFB F σ h' ⬝ u.1.1)) := by
  first | exact @GlobalTheory.CosetFJ.besselOrbit_at_badPlace_eq_congruenceTranslate | exact GlobalTheory.CosetFJ.besselOrbit_at_badPlace_eq_congruenceTranslate | (intros; apply GlobalTheory.CosetFJ.besselOrbit_at_badPlace_eq_congruenceTranslate <;> assumption)
