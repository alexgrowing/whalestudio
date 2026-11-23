import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeRowMulVecMemModulusScaledCompletion
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
theorem _root_.GlobalTheory.T.depthLatticeRow_mulVec_mem_modulus_scaledCompletion : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ Y ∈ latRow G i, ∀ (v : GlobalTheory.FinPl.Pl D) (y : Fin (G.V (.grid (i + 1) 0)).rank → AE D), y ∈ latV _ (G.Λ (.grid (i + 1) 0)) (· = v) → (e • Y) *ᵥ y ∈ GlobalTheory.FinPl.latMul _ {a | a ∈ ((G.modul : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)} (G.Λ (.grid i 0)) (· = v) := by
  first | exact @GlobalTheory.DepthRowLem.latRow_mulVec | exact GlobalTheory.DepthRowLem.latRow_mulVec | (intros; apply GlobalTheory.DepthRowLem.latRow_mulVec <;> assumption)
