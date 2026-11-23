import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCrdHolds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR

set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem colC_eq_lin_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) :
    _root_.GlobalTheory.MiTop.columnOfCoordinates W u = Formalism.IndefR.Cx.lin (fun k => D.jN u (W.P.I.eNu u (Pi.single k 1))) := by
  funext x
  exact (Fintype.linearCombination_apply ℂ _ x).symm
theorem colCrd_of_real_pack : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.ColumnCoordinateCondition W := by
  intro D L hT Gi Gl Kc Yd cX ex W u
  have hbij : Function.Bijective (Formalism.IndefR.Cx.lin (fun k => D.jN u (W.P.I.eNu u (Pi.single k 1)))) :=
    GlobalTheory.Mem.SJ.lin_bijective_of_form D.what₂.embLL (D.jN u) (D.div.Nu u).b (W.P.I.eNu u) (D.jN_basis u)
  have hrat : ∀ x, _root_.GlobalTheory.MiTop.columnOfCoordinates W u (cpt D.what₂.embLL x) = D.jN u (W.P.I.eNu u x) := fun x => by
    rw [_root_.GlobalTheory.MiTop.colC_eq_lin_alt]
    exact GlobalTheory.Mem.SJ.lin_cpt_semilinear D.what₂.embLL ((D.jN u).comp (W.P.I.eNu u).toLinearMap) x
  refine ⟨_root_.GlobalTheory.MiTop.colC_eq_lin_alt W u ▸ hbij, hrat, 1, one_pos, fun x => ?_⟩
  rw [one_mul]
  let e : (Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) ≃ₗ[ℂ] D.what₂.Mu u :=
    LinearEquiv.ofBijective (Formalism.IndefR.Cx.lin (fun k => D.jN u (W.P.I.eNu u (Pi.single k 1)))) hbij
  have hv0 : W.P.A3.A.v0 = InfinitePlace.mk D.what₂.embLL := W.Q.Rl.hv0
  have htw : ∀ a, (InfinitePlace.mk D.what₂.embLL).embedding a =
      Formalism.IndefR.Links.cj (Formalism.L2.SG.JoinSI.twQ W.P) (D.what₂.embLL a) := by
    intro a
    rw [← hv0]
    exact _root_.Formalism.L2.SG.JoinSI.embedding_eq_cj_twQ_embLL W.Q a
  have key := GlobalTheory.Mem.SJ.fnorm_cjv_eq_norm D.what₂.LL D.what₂.embLL (Formalism.L2.SG.JoinSI.twQ W.P) htw
    (GlobalTheory.Mem.SJ.colNorm_exists_im_ne_zero _) (D.div.Nu u) _ (W.P.NuC (W.P.I.wU u)) _ (W.P.I.eNu u)
    (W.P.tied.div.cols.Nu u) (D.what₂.Mu u) (D.jN u) e.symm (GlobalTheory.Mem.SJ.colNorm_normAt_column D u)
    (fun y => by
      rw [LinearEquiv.symm_symm]
      exact (congrFun (_root_.GlobalTheory.MiTop.colC_eq_lin_alt W u) _).symm.trans (hrat y)) (_root_.GlobalTheory.MiTop.columnOfCoordinates W u x)
  have hx : e.symm (_root_.GlobalTheory.MiTop.columnOfCoordinates W u x) = x := by
    rw [LinearEquiv.symm_apply_eq]
    exact congrFun (_root_.GlobalTheory.MiTop.colC_eq_lin_alt W u) x
  rw [hx] at key
  have hv : W.P.A3.fam3.base3.v0 = InfinitePlace.mk D.what₂.embLL := hv0
  rw [hv]
  exact key
end GlobalTheory.MiTop
end
