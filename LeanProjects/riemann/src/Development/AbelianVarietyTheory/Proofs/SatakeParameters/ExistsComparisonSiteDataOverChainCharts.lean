import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingYAlt
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChiFinOfGlevH
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BaseLatticeSelfDualOfLocalEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUnifPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemUnderSBOfGIdx
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiRatAllOfAdTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFractionRingGat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvCoordsIsBasisAtBaseLatticeOfStdCompanionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SiteEx

set_option maxHeartbeats 4000000 in

theorem siteD_exists : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (μ : D.what₂.Tup) (J : JIn t u μ), (D.what₂.places.resChar w) ∉ Dx.Qp μ → ∃ Z : SiteD J.Gd.herm u w hg (ex.tw.fm u μ), Z.Fo = foOf J.Hh J.St J.val ∧ SiteGood Z ∧ SiteRest Z ex.cmp ∧ ∀ i hi, Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E (Z.S i hi).B = (J.A.crd (i + 1) hi)⁻¹ := by
  intro D L hT Gi Gl Kc Dx cX ex t u w hg μ J hQ
  have hfr := GlobalTheory.Ggeo.FracLocal.isFractionRing_gat Gl u w hg
  have hrat := GlobalTheory.TwUChiRat.chiRatAll_of_adTie t u μ J.St J.A J.Hh.dt J.a J.tie J.kin
  have hpT : ∀ i (hi : i ≤ D.R.m), ¬ D.what₂.places.resChar w ∣ (J.St i hi).T := fun i hi => by
    rw [J.tie.T_eq i hi]; exact hg.2.2.2.2.2
  have hψ : ∀ i hi, PsiEx (foOf J.Hh J.St J.val i hi) (ex.cmp.embW u w hg) := fun i hi =>
    psiEx_of (foOf J.Hh J.St J.val i hi) (ex.cmp.embW u w hg) hfr (fun β => hrat (i + 1) hi β)
      (fun β => J.ord (i + 1) hi β)
  let Z : SiteD J.Gd.herm u w hg (ex.tw.fm u μ) :=
    { Fo := foOf J.Hh J.St J.val
      chFin := fun i hi => J.fin (i + 1) hi
      S := fun i hi =>
        { B := (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹
          B_lat := fun β => GlobalTheory.T.inv_coords_isBasisAt_baseLattice_of_std_companion J.Gd.herm u w hg hi ((J.St (i + 1) hi).K β).lev (J.A.crd (i + 1) hi) J.a
            (hpT (i + 1) hi) (J.base (i + 1) hi β)
          ψ := fun β => (hψ i hi β).choose
          fin := fun β => fin_of _ β _ } }
  refine ⟨Z, rfl, ⟨fun i hi => hpT (i + 1) hi, fun i hi w' hw' => ?_, fun i hi => trivial⟩, ⟨fun i hi => ?_, fun i hi β => ?_, fun i hi β cl => ?_⟩,
    fun i hi => ?_⟩
  · exact GlobalTheory.TwU.not_mem_underSB_of_gIdx t u w hg μ hQ w' (J.tie.bad (i + 1) hi w' hw')
  · show cT (sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹)).1 * gramN D (i + 1) hi *
      (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹)).1 = 1
    rw [MulEquiv.apply_symm_apply]
    exact std_of_C _ _ _ (J.pins.crd_orth (i + 1) hi)
  · exact (hψ i hi β).choose_spec
  · exact chRat_ofChiD J.chiD _ _ _
  · show Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹) = _
    exact MulEquiv.apply_symm_apply _ _

end GlobalTheory.SiteEx
