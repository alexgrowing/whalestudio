import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedHomLatticeModulusDepthMemShift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts} (G : GridData L sc) {S B : HSp D} (LS : Lat S) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ₀ : Lat B), IsSelfDualC S LS → IsSelfDualC B (idLat I Λ₀) → IsSelfDualC B (idLat (I * shiftId G) Λ₀) → ∀ z : WO S B, z ∈ latO S B (LS : Set _) (idLat I Λ₀ : Set _) (fun _ => True) → (∃ e, IsIdemSum e G.pl.W0 ∧ e • z ∈ hatMx (G.modul • homLat LS (idLat I Λ₀))) → z ∈ latO S B (LS : Set _) (idLat (I * shiftId G) Λ₀ : Set _) (fun _ => True) := by
  first | exact @GlobalTheory.DepthShift.mem_latO_shift | exact GlobalTheory.DepthShift.mem_latO_shift | (intros; apply GlobalTheory.DepthShift.mem_latO_shift <;> assumption)
