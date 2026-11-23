import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseIdealsCompletionEqOfModulusUnit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMemLatOIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentPowCompletionTrivialAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JZeroMulMemLatticeIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.staircase_ideals_completion_eq_of_modulus_unit : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (ρ : ℕ) (v : GlobalTheory.FinPl.Pl D), 0 < ρ → GlobalTheory.SeeSaw.idV ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) v = GlobalTheory.SeeSaw.idV 1 v → (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ - 1 + 1))⁻¹ * (P.stA sc ^ (2 * ρ - (ρ - 1)) * (P.stAbar sc ^ (ρ - 1 + 1))⁻¹) ≠ 0) ∧ (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ + 1))⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ (ρ + 1))⁻¹) ≠ 0) ∧ ∀ s, s ∈ GlobalTheory.SeeSaw.idV ((D.host.AAbar : GlobalTheory.SeeSaw.FI D) * (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ - 1 + 1))⁻¹ * (P.stA sc ^ (2 * ρ - (ρ - 1)) * (P.stAbar sc ^ (ρ - 1 + 1))⁻¹))⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ + 1))⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ (ρ + 1))⁻¹))⁻¹) v := by
  first | exact @GlobalTheory.StairIdealAt.completion_eq_of_modul_unit | exact GlobalTheory.StairIdealAt.completion_eq_of_modul_unit | (intros; apply GlobalTheory.StairIdealAt.completion_eq_of_modul_unit <;> assumption)
