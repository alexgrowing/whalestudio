import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameChangeWeakWeilRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frameChange_weakWeilRepresentation : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), ∃ e : GA D (reS S b) ≃* GA D S, (∀ h, e h ∈ GinfC S ↔ h ∈ GinfC (reS S b)) ∧ ∀ (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak ψ S T om → ContT ψ om → ∃ om' : GA D (reS S b) × GA D T →* Module.End ℂ (WO (reS S b) T → ℂ), IsWeak ψ (reS S b) T om' ∧ ContT ψ om' ∧ ∀ h g f, om' (h, g) (reF S T b f) = reF S T b (om (e h, g) f) := by
  first | exact @GlobalTheory.AdSpan.reframe_weil | exact GlobalTheory.AdSpan.reframe_weil | (intros; apply GlobalTheory.AdSpan.reframe_weil <;> assumption)
