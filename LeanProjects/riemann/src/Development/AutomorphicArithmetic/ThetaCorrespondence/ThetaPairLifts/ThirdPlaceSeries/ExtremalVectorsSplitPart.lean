import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalEstimateStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
end Gen
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
theorem ioExt_R2 (h : p.PointConditions') : IoExt (R2 p) := h.ioExt
theorem one_map_R2 (h : p.PointConditions') (i : Fin D.R.m) : OneMapRowR p.T (R2 p) p.κ p.v₀ (om2 p) (fun _ => 1) i := by
  have := oneMapRowR_charOf (κ := p.κ) (v₀ := p.v₀) p.O (F2 p) (phEff p.R) i (h.oneMap i)
  rw [phEff_eq_one] at this
  exact this
theorem twistedRational_R2_F2 (h : p.PointConditions') (hm : More p) : GlobalTheory.RealIndexBound.TwistedRational (R2 p) (F2 p) fun _ => 1 := by
  have hL : Links2 p := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p h hm.1
  exact GlobalTheory.T.twistedClassSums_rational_of_rayClassFields D _ _ _ _ p.T (R2 p) (F2 p) p.κ p.v₀ (fw2 p) (om2 p) hL.1 (_root_.GlobalTheory.BigOn.ioExt_R2 p h) hL.2.2.1
    hL.2.2.2.2.2.2.1 (splitPartRealisation_satisfies_qGuard p) (_root_.GlobalTheory.BigOn.one_map_R2 p h) hL.2.2.2.1 hL.2.2.2.2.1 hm.2.2.rayQ
end Point
theorem bigOn_ratSt : _root_.GlobalTheory.BigOn.RationalityStatement' :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ _ _ p h hm => _root_.GlobalTheory.BigOn.twistedRational_R2_F2 p h hm⟩⟩⟩
end GlobalTheory.BigOn
end
end
