import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseLevelRowSideTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedRowLiftDataToFittingStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdxDefsUp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardReadingTransportAndExtensionTransStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Up

set_option maxHeartbeats 4000000 in

theorem rxs_up : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)), RowsSame t t' → Nonempty (RXs t) → Nonempty (RXs t') := by
  intro K B f T w Z Wt p0 t S' N h t' hs ⟨x⟩
  have hstd : t'.r.z.Std := (GlobalTheory.T.standardReading_transport_and_extension_trans).1 B f T w Z (SRe.upL Z S' N h) t.hX Wt t.r.z t'.r.z hs.Xg hs.tr hs.R hs.core x.std
  obtain ⟨hX', r', exAt', inGeo', grpAt', grp', mu'', exact', untw', emt0', emt', etaF', rowInt', idx'⟩ := t'
  obtain ⟨z', holds', Y', Z'', tup_ix'⟩ := r'
  obtain @⟨Xg', tr', core', alg', alg_eq', R', cG', geo', pins', lev', idG', good', mu', le', Ks'⟩ := z'
  have hXg := hs.Xg
  have htr := hs.tr
  have hcore := hs.core
  have hR := hs.R
  have hcG := hs.cG
  have htup := hs.tup
  have hjA := hs.jA
  have hjA0 := hs.jA0
  have heMt := hs.eMt
  clear hs
  dsimp only at hXg htr hcore hR hcG htup hjA hjA0 heMt hstd
  subst hXg htr
  have hc := eq_of_heq hcore
  subst hc
  have ha : @Eq _ alg' t.r.z.alg :=
    Algebra.algebra_ext _ _ fun r => B.embLL.injective ((alg_eq' r).trans (t.r.z.alg_eq r).symm)
  subst ha
  have hr := eq_of_heq hR
  cases hr
  have hg := eq_of_heq hcG
  cases hg
  cases Y' with
  | mk tup' tupT' tupT_tup' tupTie' tup0' muAt' hm' hTop' hinj' Ish' Iz' IL' Kc' PY' PW' eFT' ιW' tied' prtE' prtE0' prtWE' xi'
      isomFin' frameMatch' hF' stdPsi' jA' jA0' eMt' => ?_
  dsimp only at htup hjA hjA0 heMt
  have e1 := eq_of_heq htup
  cases e1
  have e2 := eq_of_heq hjA
  cases e2
  have e3 := eq_of_heq hjA0
  cases e3
  have e4 := eq_of_heq heMt
  cases e4
  exact ⟨{
    all := {
      jA := (by with_unfolding_all exact (x.all.jA :))
      jA0 := (by with_unfolding_all exact (x.all.jA0 :))
      eMt := (by with_unfolding_all exact (x.all.eMt :))
      formsA := (by with_unfolding_all exact (x.all.formsA :))
      latA := (by with_unfolding_all exact (x.all.latA :))
      formsAtBottomLevel := (by with_unfolding_all exact (x.all.formsAtBottomLevel :))
      latA0 := (by with_unfolding_all exact (x.all.latA0 :))
      formsL := (by with_unfolding_all exact (x.all.formsL :))
      latL := (by with_unfolding_all exact (x.all.latL :))
      cen := (by with_unfolding_all exact (x.all.cen :)) }
    jA_use := (by with_unfolding_all exact (x.jA_use :))
    movedReadingSameMaps_baseReading_agrees := (by with_unfolding_all exact (x.movedReadingSameMaps_baseReading_agrees :))
    eMt_use := (by with_unfolding_all exact (x.eMt_use :))
    e := (by with_unfolding_all exact (x.e :))
    eMt0 := (by with_unfolding_all exact (x.eMt0 :))
    eMtTw := (by with_unfolding_all exact (x.eMtTw :))
    crd := (by with_unfolding_all exact (x.crd :))
    io := (by with_unfolding_all exact (x.io :))
    sha := (by with_unfolding_all exact (x.sha :))
    laws := (by with_unfolding_all exact ((Mv.lawsCore_tr (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
      ⟨(SRe.upL Z S' N h).W, (SRe.upL Z S' N h).V, (SRe.upL Z S' N h).S, (SRe.upL Z S' N h).N, (SRe.upL Z S' N h).G⟩ (K := t.r.z.core.toCore) x.laws) :))
    canon := (by with_unfolding_all exact (x.canon :))
    rank := (by with_unfolding_all exact (x.rank :))
    pb := (by with_unfolding_all exact (x.pb :))
    std := (by with_unfolding_all exact (hstd :)) }⟩

end GlobalTheory.Mem.R3.Rw.Up
end
