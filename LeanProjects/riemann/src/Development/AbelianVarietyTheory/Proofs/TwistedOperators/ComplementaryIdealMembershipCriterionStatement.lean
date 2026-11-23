import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryIdealMembershipCriterion
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
theorem _root_.GlobalTheory.T.complementary_ideal_membership_criterion : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts} (G : GridData L sc) (c : AE D), c ∈ complId (D.host.AA * G.pl.stAbar sc) → (∀ e, IsIdemSum e G.pl.W0 → e * c ∈ complId D.host.AAbar) → c ∈ complId (D.host.AA * D.host.AAbar) := by
  first | exact @GlobalTheory.XCharComb.mem_complId_AA_AAbar | exact GlobalTheory.XCharComb.mem_complId_AA_AAbar | (intros; apply GlobalTheory.XCharComb.mem_complId_AA_AAbar <;> assumption)
