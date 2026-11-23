import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingYAlt
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUnifPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormsSharpAtOfValTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplAlgLocAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChTwDGamDvdMemDGam
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoprimeAbsNormCcKOfGIdx
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComparisonSiteDataOverChainChartsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparisonDataStatementsAtSiteStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelStatementsOfJointStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteLabelsWithStepZeroClassMapStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparisonSiteChartsTwistsEqTupleChainStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteLocalIdentificationsEqStepZeroStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepBasisSpansLatticeFirstFactorAtPStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

set_option maxHeartbeats 4000000 in

theorem jointsAt_of_jIn : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (μ : D.what₂.Tup), G.LatTied hT Gi Gl → (∀ u, Nonempty (JIn t u μ)) → GlobalTheory.TwV.JointsAt t μ := by
  intro D L hT Gi Gl Kc Dx cX ex t μ hlt hJ u w hg hw
  obtain ⟨J⟩ := hJ u
  have ht : (Gl.Fl u w hg).t = D.R.t := fl_t ex u w hg
  have hm : (Gl.Fl u w hg).mm = D.R.m := fl_mm_eq ex u w hg
  obtain ⟨Z, hFo, hgood, hrest, -⟩ := GlobalTheory.T.exists_comparisonSiteData_over_chainCharts t u w hg μ J hw
  have H : CmpJHyp ex.cmp (Z.inTw (Gl.Fl u w hg) ht hT) :=
    GlobalTheory.T.comparison_data_statements_at_site J.Gd.herm u w hg ex.tw μ Z (Gl.Fl u w hg) ht hT (fun u => J.Gd.forms u) ex.cmp J.Gd.cmp (fillRec ex u w hg) hgood hrest
  have one := GlobalTheory.T.step_zero_level_statements_of_joint hT ex.cmp J.Gd u w hg J.joint0
  obtain ⟨X, hX⟩ := GlobalTheory.T.exists_labIn_c0_cls_eq_levelZeroClass hT ex.cmp J.Gd u w hg ex.tw μ Z (Gl.Fl u w hg) ht hm hgood J.rat
    (GlobalTheory.chTw_DGam_dvd_mem_DGam t u μ) one J.e0
  obtain ⟨hst, htw⟩ := GlobalTheory.T.comparisonSite_charts_twists_eq_tupleChain J.Gd.herm u w hg ex.tw μ Z (Gl.Fl u w hg) ht hT J.Hh J.St J.val hFo
  obtain ⟨hiw, hpl, hB, hpos, halg, halg0⟩ := GlobalTheory.T.site_localIdentifications_eq_stepZero hT ex.cmp J.Gd u w hg ex.tw μ Z (Gl.Fl u w hg) ht
  refine ⟨Z.lv (Gl.Fl u w hg) ht, Z.inTw (Gl.Fl u w hg) ht hT, H, X, ⟨?_⟩⟩
  exact
  { Gd := J.Gd
    St := J.St
    A := J.A
    dtU := J.Hh.dt
    a := J.a
    pins := J.pins
    tie := J.tie
    st := fun j hj => hst j hj
    e0 := J.e0
    jointCmpEmbeddingY := J.jointCmpEmbeddingY
    e0Tw := J.e0Tw
    one := one
    cls0 := fun c La _ => hX c La
    lev0 := J.lev0
    ch0 := J.ch0
    y0 := J.y0
    fr0 := J.fr0
    iw := hiw
    oneB := hB
    pos := hpos
    tw := htw
    rel := J.rel
    base := J.base
    sharp := GlobalTheory.FormsSharpTie.formsSharpAt_of_pins t u μ J.St J.A J.Hh.dt J.pins (fun _ _ => True) (fun j hj => J.val j hj.le)
    dgen := t.O_dgen u μ ▸ (t.O u μ).dgen_gen
    tied := hlt
    away := hw
    cop := t.cc_rec ▸ GlobalTheory.coprime_absNorm_ccK_of_gIdx D _ _ hg
    empty := Z.lv_empty (Gl.Fl u w hg) ht
    alg := halg
    alg0 := halg0
    lbB := GlobalTheory.T.step_basis_spans_latticeFirstFactor_at_p J.Gd.herm u w hg ex.tw μ Z (Gl.Fl u w hg) ht hT
    lb0 := GlobalTheory.TwV.LbB.lbAtB_lev0At hT ex.cmp J.Gd u w hg J.joint0
    pl := hpl
    kin := J.kin }

end GlobalTheory.TwV
