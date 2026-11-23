import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointsUnitaryCharacterEqDetPower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoints_unitaryCharacter_eq_detPower : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → V.SigOK → ∀ z : GA D V → ℂ, (∀ a ∈ GinfC V, ∀ a' ∈ GinfC V, z (a * a') = z a * z a') → (∀ a ∈ GinfC V, ‖z a‖ = 1) → ContinuousOn z (GinfC V : Set (GA D V)) → ∃ m : D.what₂.Tau → ℤ, ∀ a ∈ GinfC V, z a = detPow θ V m a := by
  first | exact @GlobalTheory.AdSpan.char_eq_detPow | exact GlobalTheory.AdSpan.char_eq_detPow | (intros; apply GlobalTheory.AdSpan.char_eq_detPow <;> assumption)
