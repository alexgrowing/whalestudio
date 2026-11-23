import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColNormExistsImNeZero
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

theorem colC_eq_lin (W : RealPack ex) (u : D.what₂.Word) :
    colC W u = Formalism.IndefR.Cx.lin (fun k => D.jN u (W.P.I.eNu u (Pi.single k 1))) := by
  funext x
  exact (Fintype.linearCombination_apply ℂ _ x).symm

theorem colCrd_holds : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), ColCrd W := by
  intro D L hT Gi Gl Kc Yd cX ex W u
  have hbij : Function.Bijective (Formalism.IndefR.Cx.lin (fun k => D.jN u (W.P.I.eNu u (Pi.single k 1)))) :=
    GlobalTheory.Mem.SJ.lin_bijective_of_form D.what₂.embLL (D.jN u) (D.div.Nu u).b (W.P.I.eNu u) (D.jN_basis u)
  have hrat : ∀ x, colC W u (cpt D.what₂.embLL x) = D.jN u (W.P.I.eNu u x) := fun x => by
    rw [colC_eq_lin]
    exact GlobalTheory.Mem.SJ.lin_cpt_semilinear D.what₂.embLL ((D.jN u).comp (W.P.I.eNu u).toLinearMap) x
  refine ⟨colC_eq_lin W u ▸ hbij, hrat, 1, one_pos, fun x => ?_⟩
  rw [one_mul]
  let e : (Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) ≃ₗ[ℂ] D.what₂.Mu u :=
    LinearEquiv.ofBijective (Formalism.IndefR.Cx.lin (fun k => D.jN u (W.P.I.eNu u (Pi.single k 1)))) hbij
  have hv0 : W.P.A3.A.v0 = InfinitePlace.mk D.what₂.embLL := W.Q.Rl.hv0
  have htw : ∀ a, (InfinitePlace.mk D.what₂.embLL).embedding a =
      Formalism.IndefR.Links.cj (Formalism.L2.SG.JoinSI.twQ W.P) (D.what₂.embLL a) := by
    intro a
    rw [← hv0]
    exact Formalism.L2.SG.JoinSI.twist_of_realT W.Q a
  have key := GlobalTheory.Mem.SJ.fnorm_cjv_eq_norm D.what₂.LL D.what₂.embLL (Formalism.L2.SG.JoinSI.twQ W.P) htw
    (GlobalTheory.Mem.SJ.colNorm_exists_im_ne_zero _) (D.div.Nu u) _ (W.P.NuC (W.P.I.wU u)) _ (W.P.I.eNu u)
    (W.P.tied.div.cols.Nu u) (D.what₂.Mu u) (D.jN u) e.symm (GlobalTheory.Mem.SJ.colNorm_normAt_column D u)
    (fun y => by
      rw [LinearEquiv.symm_symm]
      exact (congrFun (colC_eq_lin W u) _).symm.trans (hrat y)) (colC W u x)
  have hx : e.symm (colC W u x) = x := by
    rw [LinearEquiv.symm_apply_eq]
    exact congrFun (colC_eq_lin W u) x
  rw [hx] at key
  have hv : W.P.A3.fam3.base3.v0 = InfinitePlace.mk D.what₂.embLL := hv0
  rw [hv]
  exact key

end GlobalTheory.MiTop
