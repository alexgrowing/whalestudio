import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodFiberTypesAllStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceLengthTwistedPlacesOfHeckeIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPlaceInnerProductClassSumRowsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatIntMember
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientBuiltLocalHypothesisStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.EtaMem

open GlobalTheory.CoefDuty GlobalTheory.HeightCounting.Up

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem etaJ_built : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PtSt hL → AllSt fun _ _ _ _ _ P x => ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → ∀ j v, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : D'.what₂.places.Pl, HEq v' v → D'.what₂.etaJ j v' = P.q.eta j v := by
  intro hPr hL hPt
  have hG := GlobalTheory.T.good_fiber_types_all hPr hL
  have hI := GlobalTheory.T.twistedPlace_innerProduct_classSum_rows
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hPr.what₂.cheb
  unfold PtSt at hPt
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
  have hlat := GlobalTheory.CoefDuty.latInt_member (Dof x) (cfOf x) l.a.jE l.a.A l.mt.M l.c.ch l.c.tp.tup hmt big L hB
  have hsum : SumTw (Dof x) l.mt.M := g.2 hKP w hpin x.o.Z P.Wt P.hX x.m.z x.s.p0 x.r.Y x.m.intersectionNumber_baseChange x.m.exAt x.m.inGeo
    x.fits.grp x.fits.grpAt l.mt.M l.c.tp.tup l.c.ch.Q l.mt.ad hmt
  obtain ⟨Sp, ⟨Au⟩, hss⟩ := hB
  obtain ⟨Hk, -⟩ := GlobalTheory.FitHecke.heckeOpen_withLoc (Dof x) (cfOf x) l.a.jE l.a.A (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL
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
  exact GlobalTheory.T.coefficient_built_local_hypothesis hPr hL hKP hF hS x l big L hB0 hO (mtL L l.mt.M) cover l.c.ch.Q hstd hlat.1 hlat.2 Hk.hecke Hk.rational Hk.av hcls hEig hIso h42 hZ hgood

end GlobalTheory.EtaMem

end
