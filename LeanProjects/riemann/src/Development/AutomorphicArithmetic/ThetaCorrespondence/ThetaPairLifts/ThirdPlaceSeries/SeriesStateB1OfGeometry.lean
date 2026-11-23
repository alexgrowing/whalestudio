import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewTwistLamFull
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestageCopyRealStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FactsStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3.Tr
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
namespace GlobalTheory.HeightCounting.SerCopy
theorem series_state_b1_of_geometry_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F}
    {F : Face3 D A3} {X0 : BaseLevelRowSide D} {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    {cf cf' : CharFrame D} (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)) (n : InRat Y cG)
    (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    {Pq Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {Rw : RowSide D} {kKs hk}
    {hk' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j)} {eig θ}
    (Bs : SideB D cf' Rw (lowAll D) Pq' (ratDatR R cG kKs hk) hk' eig θ) (YS : NExpRealS R cG (ratDatR R cG kKs hk))
    (eF : YS.eF = Bs.eF) (fi : ∀ i x, HEq ((YS.fi i).e x) x) (ser : SerAt YS g.v₀ Bs.exp PV cf' Pq') (tau : TauTrue Bs.exp)
    (e1 : cf' = cf) (e2 : Rw = a.A.row) (e3 : Pq' = Pq) (e4 : HEq hk' n.In.hL) (e5 : eig = n.In.eig) (e6 : θ = n.In.θ)
    (h1 : ∀ i, n.In.Sb ⊆ D.ntw.S0 i) (h2 : ∀ i, OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D))) :
    Nonempty (_root_.GlobalTheory.HeightCounting.SeriesData g a n PV Pq) := by
  obtain rfl : kKs = n.kKs := RingHom.ext fun y => Subtype.ext ((hk y).trans (n.hk y).symm)
  subst e1 e2 e3 e5 e6
  cases e4
  exact ⟨{ Bs := Bs, Sb_le := h1, rootsOfUnityRing_le_wittIntegers := h2, lam := ⟨ser.lam, ser.lam_ok, ser.lam_teich, ser.lam_C, ser.lam_q, ser.lam_tie⟩
           YS := YS, eF := eF, fi := fi, ser := ser, tau := tau }⟩
variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
theorem pre_at_of_side_b_tau_true_lam_ok (hA : GlobalTheory.Published.GlobalArtinReciprocity) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hK : K.Over B.toPre)
    (hS : Start K B f T w) (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x)
    (hB : ∃ Bs : SideB (Dof x) (cfOf x) l.a.A.row (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig l.rat.In.θ, TauTrue Bs.exp)
    (hSb : ∀ i, l.rat.In.Sb ⊆ (Dof x).ntw.S0 i) (hZ : ∃ Z : GlobalTheory.LamTie.LamDat (Dof x), Z.Ok) :
    PreAt (P := P) x.m.z l.a.A.row l.Pq l.rat.In.hL l.rat.In.eig l.rat.In.θ := by
  obtain ⟨h1, h2, h3, h4, -⟩ := _root_.GlobalTheory.T.isChoice_of_start_of_over hL hK hS x l.toLA
  obtain ⟨Bs, hτ⟩ := sideB_tau_congr h4.symm rfl rfl HEq.rfl hB
  exact ⟨h4, l.rat.kKs, l.rat.hk, l.rat.In.hL, HEq.rfl, Bs, x.r.Y.hF, hτ,
    GlobalTheory.T.exists_newThetaData_series_classSums_lattices hA (Dof x) _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG l.rat.kKs l.rat.hk _ _ _ _ _ Bs l.rat.In.Sb x.m.z.geo.v₀ x.r.Y.hF
      x.m.z.pins x.m.intersectionNumber_baseChange (fun j => x.m.z.geo.fw.hv₀ j _) x.m.z.geo.fw.ks l.rat.rat.hecke hSb hτ (h4 ▸ l.a.A.chr) (h4 ▸ l.a.val)
      l.a.elem.split l.Pq_over h1 h2 hZ h3⟩
theorem pre_at_twisted_copy_of_side_b_tau_true (hA : GlobalTheory.Published.GlobalArtinReciprocity) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hK : K.Over B.toPre)
    (hS : Start K B f T w) (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x))
    (hB : ∃ Bs : SideB N.toD7 (N.cf (cfOf x)) (N.row l.a.A.row) (lowAll (Dof x)) l.Pq (N.rat l.rat.S) l.rat.In.hL l.rat.In.eig
      l.rat.In.θ, TauTrue Bs.exp)
    (hSb : ∀ i, l.rat.In.Sb ⊆ N.tw.S0 i) (hZ : ∃ Z : GlobalTheory.LamTie.LamDat N.toD7, Z.Ok) :
    PreAt (P := P) (datTw x N) ((by with_unfolding_all exact ((N.row l.a.A.row) :))) ((by with_unfolding_all exact (l.Pq :))) l.rat.In.hL ((by with_unfolding_all exact (l.rat.In.eig :))) ((by with_unfolding_all exact (l.rat.In.θ :))) := by
  obtain ⟨x', l', ho, -, hrow, hPq, hS', hSb', hhL, heig, hθ, hR, hcG, hgeo⟩ := _root_.GlobalTheory.T.twisted_state_transport_heq_levels' hL x l N
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at ho
  subst ho
  have hz : m'.z = datTw x N := moved_eq_datTw x N m' copy' hR hcG hgeo
  have e1 : l'.a.A.row = (by with_unfolding_all exact ((N.row l.a.A.row) :)) := (by with_unfolding_all exact ((eq_of_heq hrow) :))
  have e2 : l'.Pq = (by with_unfolding_all exact (l.Pq :)) := (by with_unfolding_all exact ((eq_of_heq hPq) :))
  have e3 : l'.rat.S = (by with_unfolding_all exact ((N.rat l.rat.S) :)) := (by with_unfolding_all exact ((eq_of_heq hS') :))
  have e4 : l'.rat.In.Sb = (by with_unfolding_all exact (l.rat.In.Sb :)) := (by with_unfolding_all exact ((eq_of_heq hSb') :))
  have e5 : l'.rat.In.eig = (by with_unfolding_all exact (l.rat.In.eig :)) := (by with_unfolding_all exact ((eq_of_heq heig) :))
  have e6 : l'.rat.In.θ = (by with_unfolding_all exact (l.rat.In.θ :)) := (by with_unfolding_all exact ((eq_of_heq hθ) :))
  have h := _root_.GlobalTheory.HeightCounting.SerCopy.pre_at_of_side_b_tau_true_lam_ok hA hK hS _ l' (by
    rewrite [e1, e5, e6]
    exact sideB_tau_congr rfl e2.symm e3.symm hhL.symm ((by with_unfolding_all exact (hB :)))) (by rewrite [e4]; exact (by with_unfolding_all exact (hSb :))) ((by with_unfolding_all exact (hZ :)))
  exact preAt_congr hz e1 e2 hhL e5 e6 h
section Install
variable {x : St P} {N₁ : TwNew (Dof x)} {kKs : (datTw x N₁).core.Q.c.F →+* ↥(DN x N₁).LL0}
  {hk : ∀ y, ((kKs y : ↥(DN x N₁).LL0) : (DN x N₁).what₂.LL) = algebraMap (datTw x N₁).core.Q.c.F (DN x N₁).what₂.LL y}
  {cf : CharFrame (DN x N₁)} {Rw : RowSide (DN x N₁)}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (DN x N₁).host.E)) → PlE (DN x N₁).host} {hf eig θ}
  {Bs : SideB (DN x N₁) cf Rw (lowAll (DN x N₁)) Pq (ratDatR (datTw x N₁).R (datTw x N₁).cG kKs hk) hf eig θ} {hF}
  (p : PreTie (ysOf Bs) (datTw x N₁).geo.v₀ Bs.exp hF Pq)
theorem series_state_b1_twist_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hτ : TauTrue Bs.exp) (hC : cf = TC.cf w.I w.l (oTw x N₁).Z)
    (hu : GlobalTheory.UnivChar.IsUnivChar (DN x N₁).nexp) (ho : NoOff (DN x N₁))
    (z : Dat (w.st (oTw x (nP p)).Z) w.I P.hX T P.Wt) (hz : z = datTw x (nP p)) {X0 : BaseLevelRowSide (DN x (nP p))}
    (Y : R3.Read z.R.toRealDat z.F.lv2 X0) (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL (DN x (nP p)) (TC.cf w.I w.l (oTw x (nP p)).Z) (repOf Y)) (n : InRat Y z.cG)
    (PV : ∀ j : Fin (DN x (nP p)).R.m, principalLevelFrame.RowPsi (Vc (DN x (nP p)) j) (DN x (nP p)).R.nV) {hF'}
    (hPV : ∀ j, GlobalTheory.MtRead.IdFrame hF' (PV j))
    (Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield (DN x (nP p)).host.E)) → PlE (DN x (nP p)).host)
    (hZ : ∃ Z : GlobalTheory.LamTie.LamDat (DN x (nP p)), Z.Ok ∧ Z.Teich ∧ Z.C = TC.cf w.I w.l (oTw x (nP p)).Z ∧
      Z.q0 = AbsolutelyIrreducibleSpan.q0 (DN x (nP p)) ∧ GlobalTheory.LamTie.IsLamTieFull (DN x (nP p)).ntw Z)
    (e2 : HEq a.A.row ((kwP p).row Rw)) (e3 : HEq Pq' Pq) (e4 : HEq n.In.hL hf) (e5 : HEq n.In.eig eig) (e6 : HEq n.In.θ θ)
    (h1 : ∀ i, n.In.Sb ⊆ (DN x (nP p)).ntw.S0 i)
    (h2 : ∀ i, OverSet (DN x (nP p)) ((DN x (nP p)).ntw.S0 i) (insert ((DN x (nP p)).ntw.l i) (lowAll (DN x (nP p))))) :
    Nonempty (_root_.GlobalTheory.HeightCounting.SeriesData z.geo a n PV Pq') := by
  subst hz
  obtain ⟨Z, z1, z2, z3, z4, z5⟩ := hZ
  have e1 : ((by with_unfolding_all exact (((kwP p).cf cf) :)) : CharFrame (DN x (nP p))) = TC.cf w.I w.l (oTw x (nP p)).Z := (by with_unfolding_all exact ((congrArg (kwP p).cf hC) :))
  exact _root_.GlobalTheory.HeightCounting.SerCopy.series_state_b1_of_geometry_alt _ a n PV (bsP p) (ysP p) ((by with_unfolding_all exact ((Eq.refl Bs.eF) :))) ((by with_unfolding_all exact ((ysOf_fi Bs) :)))
    ((by with_unfolding_all exact ((serP p hu ho Bs.bsup PV hPV Z ⟨z1, z2, z3.trans e1.symm, z4, z5⟩) :))) ((by with_unfolding_all exact (hτ :))) e1 ((by with_unfolding_all exact ((eq_of_heq e2).symm :)))
    ((by with_unfolding_all exact ((eq_of_heq e3).symm :))) ((by with_unfolding_all exact (e4.symm :))) ((by with_unfolding_all exact ((eq_of_heq e5).symm :))) ((by with_unfolding_all exact ((eq_of_heq e6).symm :))) h1 h2
end Install
end GlobalTheory.HeightCounting.SerCopy
end
end
