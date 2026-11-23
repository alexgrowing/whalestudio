import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CornerCoordinateAutomatic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mi
namespace GlobalTheory.MiS.Check
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem used_all_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) : Formalism.IndefR.RecTie.Used0 D (W.P.I.tup t) := by
  rcases W.Q.charW.tup.mu_used t with h | ⟨w, h⟩
  · rw [h]; exact used_base W.P
  · right
    have e : W.Q.Rl.mu = W.P.S0.μ := mu_eq_of_heq W.P W.Q.zs _ W.Q.s0
    refine ⟨D.plEq.symm w, ?_⟩
    rw [W.P.tied.div.tup.muAt, Equiv.apply_symm_apply, ← h, e]
    rfl
end GlobalTheory.MiS.Check
end
end
