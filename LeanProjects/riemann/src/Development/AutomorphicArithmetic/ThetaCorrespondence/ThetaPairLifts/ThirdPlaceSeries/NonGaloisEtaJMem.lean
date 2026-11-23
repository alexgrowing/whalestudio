import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaEventuallyAgreesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FirstTermConditionHoldsAllStages
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatIntMember
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpenWithLoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EtaJLocalCompatibility
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.EtaMem
open GlobalTheory.CoefDuty GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_etaJ_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PointStatement hL → AllSt fun _ _ _ _ _ P x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → ∀ j v, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : D'.what₂.places.Pl, HEq v' v → D'.what₂.etaJ j v' = P.q.eta j v := by
  intro hPr hL hPt
  have hG := _root_.GlobalTheory.T.allSt_goodFTAll_of_levelA hPr hL
  have hI := GlobalTheory.T.twistedPlace_innerProduct_classSum_rows
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hPr.what₂.cheb
  unfold _root_.GlobalTheory.HeightCounting.Up.PointStatement at hPt
  unfold AllSt at hPt hG ⊢
  unfold OverRows at hI
  unfold StepW GroupRetwisting.Step EvLgG at hPt hG ⊢
  refine EvG.imp (EvG.inter (EvG.inter hPt hG) hI) fun K _ _ _ _ h => ?_
  refine large₂.imp (large₂.inter (large₂.inter h.1.1 h.1.2) h.2) fun B f T _ g => ?_
  intro hKP hF _ w hS P x l
  have hpin : ColPin w := hS.1.some
  obtain ⟨big, hbig⟩ := g.1.1 hKP hF trivial w hS P x l
  refine ⟨big, fun L hB hO => ?_⟩
  have hB0 := hB
  obtain ⟨hconds, hEig, hIso⟩ := hbig L hB
  obtain ⟨-, -, h42, hZ⟩ := hconds hO
  have hgood : GoodFTAll (withLoc L) := g.1.2 hKP hF trivial w hS P x l.toLA
  have hmt : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
    have h0 := l.mt.mt
    have e1 := l.c.xi_eq
    have e2 := l.c.Q_eq
    unfold TupTied.tup
    rw [e1, e2]
    exact h0
  have hlat := _root_.GlobalTheory.CoefDuty.latInt_member_alt (Dof x) (cfOf x) l.a.jE l.a.A l.mt.M l.c.ch l.c.tp.tup hmt big L hB
  have hsum : SumTw (Dof x) l.mt.M := g.2 hKP w hpin x.o.Z P.Wt P.hX x.m.z x.s.p0 x.r.Y x.m.intersectionNumber_baseChange x.m.exAt x.m.inGeo
    x.fits.grp x.fits.grpAt l.mt.M l.c.tp.tup l.c.ch.Q l.mt.ad hmt
  obtain ⟨Sp, ⟨Au⟩, hss⟩ := hB
  obtain ⟨Hk, -⟩ := _root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt (Dof x) (cfOf x) l.a.jE l.a.A (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL
    l.rat.In.eig l.rat.In.θ l.b.Bs l.mt.M l.c.ch l.c.tp l.c.side hmt l.a.elem.star l.a.elem.int l.a.elem.split
    (hcheb (Dof x)) big L Sp Au
  let cover : NormalizedLocalCompatibility (withLoc L) (mtL L l.mt.M) :=
    { B := { Sp.B with }
      Q_eq := Sp.Q_eq
      mx := Sp.mx
      mx_max := Sp.mx_max
      mx_inj := Sp.mx_inj
      mx_all := Sp.mx_all
      phO := Sp.phO
      phK := Sp.phK
      phK_alg := Sp.phK_alg
      phK_emb := Sp.phK_emb
      Psi := Sp.Psi
      Psi_inj := Sp.Psi_inj
      Psi_range := Sp.Psi_range
      Psi_pr := Sp.Psi_pr
      ptX := Sp.ptX
      ptX_hT := Sp.ptX_hT
      iotaC := Sp.iotaC
      iotaC_coh := fun j w i h z => by
        have e1 : (withLoc L).naut.iotaQ i = Sp.iq i := Au.iotaQ i
        have e2 : (withLoc L).naut.iotaQC i = qCast ((withLoc L).nd.w_l i) (l.a.A.pl.ι ((withLoc L).nd.w i)) := Au.iotaQC i
        unfold iotaOC
        rw [RingHom.comp_apply, RingHom.comp_apply, e1, e2]
        exact Sp.iotaC_coh j w i h z }
  have hstd : HeckeStdTw cover.B := heckeStdTw_of_std Sp.std
  have hcls : ∀ i, CoefDuty.ClassSum ((mtL L l.mt.M).loc i) := by
    intro i
    have hj := L.X.j_range i
    have h0 := hsum (L.X.w i) (L.X.w_tw i) (L.X.j i) hj.1 hj.2
    exact GlobalTheory.FitHecke.mt_transport l.mt.M (fun μ j m => CoefDuty.ClassSum m) (L.X.mu_w i).symm rfl hj.1 hj.2 hj.1 hj.2 h0
  exact _root_.GlobalTheory.T.etaJ_local_compatibility_alt hPr hL hKP hF hS x l big L hB0 hO (mtL L l.mt.M) cover l.c.ch.Q hstd hlat.1 hlat.2 Hk.hecke Hk.rational Hk.av hcls hEig hIso h42 hZ hgood
end GlobalTheory.EtaMem
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_etaJ_eq_eta_of_levelC : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PointStatement hL → AllSt fun _ _ _ _ _ P x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → ∀ j v, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : D'.what₂.places.Pl, HEq v' v → D'.what₂.etaJ j v' = P.q.eta j v := by
  first | exact @_root_.GlobalTheory.EtaMem.exists_etaJ_alt | exact _root_.GlobalTheory.EtaMem.exists_etaJ_alt | (intros; apply _root_.GlobalTheory.EtaMem.exists_etaJ_alt <;> assumption)
end
end
