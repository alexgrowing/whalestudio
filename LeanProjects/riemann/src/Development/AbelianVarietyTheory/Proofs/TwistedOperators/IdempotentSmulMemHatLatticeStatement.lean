import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSmulMemHatLattice
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_smul_mem_hat_lattice : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), v ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) → v ∈ latBig G i → ∀ e : AE D, IsIdemSum e G.pl.W0 → e • v ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := by
  first | exact @GlobalTheory.DepthBig.smul_mem_hatMx_of_mem_latBig | exact GlobalTheory.DepthBig.smul_mem_hatMx_of_mem_latBig | (intros; apply GlobalTheory.DepthBig.smul_mem_hatMx_of_mem_latBig <;> assumption)
