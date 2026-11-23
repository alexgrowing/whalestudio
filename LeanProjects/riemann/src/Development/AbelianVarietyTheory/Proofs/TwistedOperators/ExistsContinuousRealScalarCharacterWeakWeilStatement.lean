import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRealScalarCharacterWeakWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_realScalar_character_weakWeil : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ContT C.ψ om → ∃ z : GA D T → ℂ, (∀ a ∈ GinfC T, ∀ a' ∈ GinfC T, z (a * a') = z a * z a') ∧ (∀ a ∈ GinfC T, ‖z a‖ = 1) ∧ ContinuousOn z (GinfC T : Set (GA D T)) ∧ ∀ B, C.IsB B → ∀ a ∈ GinfC T, RealScal C om B a (z a) := by
  first | exact @GlobalTheory.AdSpan.RealChar.realScal_character | exact GlobalTheory.AdSpan.RealChar.realScal_character | (intros; apply GlobalTheory.AdSpan.RealChar.realScal_character <;> assumption)
