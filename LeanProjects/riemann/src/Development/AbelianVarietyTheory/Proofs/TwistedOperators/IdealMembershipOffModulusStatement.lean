import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdealMembershipOffModulus
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
theorem _root_.GlobalTheory.T.ideal_membership_off_modulus : All fun {D} _ _ _ {G} _ _ => ∀ v ∈ G.pl.S0, ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ s ∈ idAt D (· = v), s ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D * ((G.modul : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v → e * s ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) v → s ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D) v := by
  first | exact @GlobalTheory.DepthIdeal.mem_dI_of_half | exact GlobalTheory.DepthIdeal.mem_dI_of_half | (intros; apply GlobalTheory.DepthIdeal.mem_dI_of_half <;> assumption)
