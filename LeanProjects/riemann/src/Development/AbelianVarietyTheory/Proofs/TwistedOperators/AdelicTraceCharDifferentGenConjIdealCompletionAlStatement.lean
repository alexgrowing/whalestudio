import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicTraceCharDifferentGenConjIdealCompletionAl
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
theorem _root_.GlobalTheory.T.psiE_xi0_mul_cA_eq_one_of_mem_complId : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) → ∀ s ∈ complId (D.host.AA * D.host.AAbar), psiE ψ (incA D D.host.xi0 * cA D s) = 1 := by
  first | exact @GlobalTheory.XCharBF.adelicTraceChar_differentGen_conj_idealCompletion | exact GlobalTheory.XCharBF.adelicTraceChar_differentGen_conj_idealCompletion | (intros; apply GlobalTheory.XCharBF.adelicTraceChar_differentGen_conj_idealCompletion <;> assumption)
