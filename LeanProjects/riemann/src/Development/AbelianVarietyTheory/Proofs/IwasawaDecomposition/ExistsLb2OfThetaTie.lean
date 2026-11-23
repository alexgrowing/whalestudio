import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedThTw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StateB2OfRationalData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpTh
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataLaterStagesWithNewTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedReadingTransportedNewTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesAtThetaTwist
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem lb2_of_theta_twist (x : St P) (l : SeriesLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp)
    (hT : GlobalTheory.GeoTie.ThetaTie l.b.YS x.m.z.geo.fw th)
    (m : Moved (oTw x (thTw (Dof x) th))) (hm : m.z = datTw x (thTw (Dof x) th)) (hc : m.Copy) (hh : m.Coh)
    (r : ReadPk m (sideTw x (thTw (Dof x) th))) (hp : r.Pin) (l' : LI hL (stTw x _ m hc hh r hp))
    (h1 : HEq l'.a.A.row ((thTw (Dof x) th).row l.a.A.row)) (h2 : HEq l'.Pq l.Pq)
    (h3 : HEq l'.rat.S ((thTw (Dof x) th).rat l.rat.S)) (h4 : HEq l'.rat.In.Sb l.rat.In.Sb) (h5 : HEq l'.rat.In.hL l.rat.In.hL)
    (h6 : HEq l'.rat.In.eig l.rat.In.eig) (h7 : HEq l'.rat.In.θ l.rat.In.θ)
    (mt : InMt r.Y (cfOf (stTw x _ m hc hh r hp)) w.I.xi (QOf P))
    (hPV : mt.ad.PV = fun i => (by with_unfolding_all exact ((rowPsi (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z (l.mt.ad.PV (by with_unfolding_all exact (i :)))) :)))
    (hser : Nonempty (SerAt (ysTh x l th) (datTw x (thTw (Dof x) th)).geo.v₀ (expTh x l th) (pvTh x l.toLI th)
      (TC.cf w.I w.l (oTw x (thTw (Dof x) th)).Z) l.Pq)) :
    Nonempty (ModuliPointsState (stTw x _ m hc hh r hp).m.z.geo l'.a l'.rat mt.ad.PV l'.Pq) := by
  rcases m with ⟨z⟩
  dsimp only at hm
  subst hm
  exact hser.elim fun s => state_b2_of_rational_data ((by with_unfolding_all exact (((thTw (Dof x) th).row l.a.A.row) :))) ((by with_unfolding_all exact (((thTw (Dof x) th).rat l.rat.S) :))) ((by with_unfolding_all exact (l.rat.In.hL :)))
    ((by with_unfolding_all exact (l.rat.In.eig :))) ((by with_unfolding_all exact (l.rat.In.θ :))) ((by with_unfolding_all exact (l.rat.In.Sb :)))
    _ ((by with_unfolding_all exact (l.Pq :)))
    ((by with_unfolding_all exact (h1 :))) ((by with_unfolding_all exact (h3 :))) ((by with_unfolding_all exact (h5 :))) ((by with_unfolding_all exact (h6 :))) ((by with_unfolding_all exact (h7 :))) ((by with_unfolding_all exact (h4 :))) hPV ((by with_unfolding_all exact (h2 :)))
    ((by with_unfolding_all exact ((bsTw l.b.Bs th) :))) ((by with_unfolding_all exact (l.b.Sb_le :))) ((by with_unfolding_all exact (l.b.rootsOfUnityRing_le_wittIntegers :))) ((by with_unfolding_all exact ((lam_thTw th l.b.lam) :)))
    ((by with_unfolding_all exact ((ysTh x l th) :)))
    ((by with_unfolding_all exact (l.b.eF :))) ((by with_unfolding_all exact (l.b.fi :)))
    ((by with_unfolding_all exact (s :)))
    ((by with_unfolding_all exact (l.b.tau :)))
    ⟨⟨fun i j b => ⟨(by with_unfolding_all exact ((hT.side ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b).pt :)), (by with_unfolding_all exact ((hT.side ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b).cover :)),
      (by with_unfolding_all exact ((hT.side ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b).ev_eq :)), (by with_unfolding_all exact ((hT.side ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b).fmUr :)), (by with_unfolding_all exact ((hT.side ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b).hk :)),
      (by with_unfolding_all exact ((hT.side ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b).hk_none :))⟩, (by with_unfolding_all exact (hT.isUnramified₂ :))⟩⟩

theorem points_carry : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : SeriesLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp), GlobalTheory.GeoTie.ThetaTie l.b.YS x.m.z.geo.fw th → ∃ x' : St P, Nonempty (StrictHenselianAcyclic hL x') ∧ x'.o = oTw x (thTw (Dof x) th) ∧ HEq x'.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z x.m.z.R.toRealDat.toLevCh) := by
  intro hL K B f T w P x l th hT
  have hser := GlobalTheory.T.series_at_theta_twist hL x l th
  obtain ⟨m, hm, hc, hh⟩ := GlobalTheory.T.exists_movedData_laterStagesWithNewTwist x (thTw (Dof x) th)
  obtain ⟨r, hp, hrep, hj, he⟩ := GlobalTheory.T.exists_normalisedReading_transported_newTwist x _ m hm hc hh
  obtain ⟨l', h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.T.read_package_twist_heq hL x l.toLI _ m hm hc hh r hp hrep hj he
  obtain ⟨mt, hPV⟩ := mt_thTw x l.toLI th m hm hc hh r hp hj
  refine ⟨stTw x _ m hc hh r hp, ?_, rfl, ?_⟩
  · exact (lb2_of_theta_twist x l th hT m hm hc hh r hp l' h1 h2 h3 h4 h5 h6 h7 mt hPV hser).elim fun b => ⟨{ toLI := { l' with mt := mt }, b := b }⟩
  · show HEq m.z.R.toRealDat.toLevCh _
    rw [hm]
    exact (by with_unfolding_all exact ((HEq.refl (datTw x (thTw (Dof x) th)).R.toRealDat.toLevCh) :))

end GlobalTheory.HeightCounting.Up
end
