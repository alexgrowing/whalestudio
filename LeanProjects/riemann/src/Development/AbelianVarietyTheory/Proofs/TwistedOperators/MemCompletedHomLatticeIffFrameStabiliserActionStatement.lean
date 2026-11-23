import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffFrameStabiliserAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedHomLattice_iff_frameStabiliser_action : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop) (u : WO S T), u ∈ latO S T ΛS ΛT Pv ↔ actO S T g h u ∈ latO S T ΛS ΛT Pv := by
  first | exact @GlobalTheory.LatStab.mem_latO_iff_actO_mem | exact GlobalTheory.LatStab.mem_latO_iff_actO_mem | (intros; apply GlobalTheory.LatStab.mem_latO_iff_actO_mem <;> assumption)
