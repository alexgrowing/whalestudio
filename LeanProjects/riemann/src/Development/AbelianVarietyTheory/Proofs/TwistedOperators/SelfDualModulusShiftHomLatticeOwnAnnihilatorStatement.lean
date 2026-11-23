import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualModulusShiftHomLatticeOwnAnnihilator
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
theorem _root_.GlobalTheory.T.selfDual_modulus_shift_hom_lattice_own_annihilator : OnStd fun {D} _ _ {sc} {G} W _ => ∀ i, i < D.R.m → ∀ u' : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (fun _ => True) u' → (∀ u ∈ latBig G i, W.ψ (symplO _ _ u u') = 1) → u' ∈ latBig G i := by
  first | exact @GlobalTheory.AscFin.latBig_ann_right | exact GlobalTheory.AscFin.latBig_ann_right | (intros; apply GlobalTheory.AscFin.latBig_ann_right <;> assumption)
