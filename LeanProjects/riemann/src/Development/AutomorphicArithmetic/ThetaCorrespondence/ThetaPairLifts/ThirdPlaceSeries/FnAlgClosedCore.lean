import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuBoundNotAlgebraicallyClosed
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CoreDesc
theorem fnAlgClosed_core_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (hR : _root_.GlobalTheory.CovTop.RowsTAlt p) (j : ℕ) (hj : InR D j) : FnAlgClosed (p.T.Q.Xo j) p.T.Q.c := by
  have hc := hR.1.ties.core
  have hpin : p.T.Q.Pins := hc.laws.pins
  have hpos : 0 < D.host.g 0 * D.host.g 1 * D.host.pde :=
    Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) D.host.pde_prime.pos
  refine GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_pins D p.T.Q hpin hc.canon _ hpos hc.field₁.curve j hj p.T.Q.l
    (p.T.Q.Xo j) p.T.Q.c hpin.2.1.2 ?_ rfl
  rw [hpin.2.1.1]
  exact Dvd.intro _ rfl
end GlobalTheory.CoreDesc
end
