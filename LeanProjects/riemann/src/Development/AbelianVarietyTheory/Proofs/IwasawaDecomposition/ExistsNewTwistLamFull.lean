import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealIoX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScalarP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTauFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedEqDatTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedStateTransportHeqLevelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondStepNoFormsOutsideLiftRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceOfLocalAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistDataLowerBlockUniversalCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewThetaDataSeriesClassSumsLatticesStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3.Tr
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.SerCopy

def lamT {D : D7} (N : TwNew D) (Z : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.LamDat N.toD7 := ⟨N.cf Z.C, Z.q0, Z.w0, Z.c, Z.chi⟩

theorem lamT_spec {D : D7} (N : TwNew D) {cf : CharFrame D} {Z : GlobalTheory.LamTie.LamDat D}
    (h : Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull N.tw Z) :
    (lamT N Z).Ok ∧ (lamT N Z).Teich ∧ (lamT N Z).C = N.cf cf ∧ (lamT N Z).q0 = AbsolutelyIrreducibleSpan.q0 N.toD7 ∧
      GlobalTheory.LamTie.IsLamTieFull N.toD7.ntw (lamT N Z) :=
  ⟨⟨(by with_unfolding_all exact (h.1.places :)), (by with_unfolding_all exact (h.1.aux :)), (by with_unfolding_all exact (h.1.big :))⟩, (by with_unfolding_all exact (h.2.1 :)), congrArg N.cf h.2.2.1, (by with_unfolding_all exact (h.2.2.2.1 :)), (by with_unfolding_all exact (h.2.2.2.2 :))⟩

theorem exists_prepared (hA : GlobalTheory.Published.GlobalArtinReciprocity) {D : D7} {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ} (Bs : SideB D cf Rw low Pq S hL eig θ) (hV : ValLL0 D cf)
    (hr : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) :
    ∃ N : TwNew D, (∀ Z : GlobalTheory.LamTie.LamDat D, GlobalTheory.LamTie.IsLamTieFull D.ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z) ∧
      (∀ i', ∃ i, N.tw.S0 i' = D.ntw.S0 i ∧ N.tw.l i' = D.ntw.l i) ∧ NoOff N.toD7 ∧ GlobalTheory.UnivChar.IsUnivChar N.toD7.nexp ∧
      ∃ Bs' : SideB N.toD7 (N.cf cf) (N.row Rw) low Pq (N.rat S) hL eig θ, TauTrue Bs'.exp := by
  obtain ⟨N, h1, h2, h3, ⟨B1⟩⟩ := GlobalTheory.T.secondStep_no_forms_outside_liftRange D cf Rw low Pq S hL eig θ Bs
  obtain ⟨τ, hτ⟩ := GlobalTheory.TwInputs.exists_tau_family hA N.toD7 _ _ _ _ _ _ _ _ B1
    ⟨(by with_unfolding_all exact (hV.mu0 :)), (by with_unfolding_all exact (hV.eta :)), (by with_unfolding_all exact (hV.chiPsi :)), (by with_unfolding_all exact (hV.del :)), (by with_unfolding_all exact (hV.del' :))⟩ ((by with_unfolding_all exact (hr :)))
  obtain ⟨⟨tw, ex, h0, th, br, hbr⟩, e, g1, g2, B2, g3⟩ := GlobalTheory.T.exists_twistData_lowerBlock_universalCharacter N.toD7 _ _ _ _ _ _ _ _ B1 τ hτ
  dsimp only at e
  subst e
  exact ⟨⟨N.tw, (by with_unfolding_all exact (ex :)), (by with_unfolding_all exact (h0 :)), (by with_unfolding_all exact (th :)), (by with_unfolding_all exact (br :)), (by with_unfolding_all exact (hbr :))⟩, h1, h2, (by with_unfolding_all exact ((g1 h3) :)), (by with_unfolding_all exact (g2 :)), (by with_unfolding_all exact (B2 :)), (by with_unfolding_all exact (g3 :))⟩

theorem sideB_tau_congr {D : D7} {cf cf' : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S S' : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {hL' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S'.WL j)}
    {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (e1 : cf = cf') (e4 : Pq = Pq') (e5 : S = S') (e6 : HEq hL hL')
    (h : ∃ Bs : SideB D cf Rw low Pq S hL eig θ, TauTrue Bs.exp) : ∃ Bs : SideB D cf' Rw low Pq' S' hL' eig θ, TauTrue Bs.exp := by
  subst e1 e4 e5
  cases e6
  exact h

theorem nonempty_seriesState {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F}
    {F : Face3 D A3} {X0 : BaseLevelRowSide D} {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    {cf cf' : CharFrame D} (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (a : StA hL D cf (repOf Y)) (n : InRat Y cG)
    (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    {Pq Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {Rw : RowSide D} {kKs hk}
    {hk' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j)} {eig θ}
    (Bs : SideB D cf' Rw (lowAll D) Pq' (ratDatR R cG kKs hk) hk' eig θ) (YS : NExpRealS R cG (ratDatR R cG kKs hk))
    (eF : YS.eF = Bs.eF) (fi : ∀ i x, HEq ((YS.fi i).e x) x) (ser : SerAt YS g.v₀ Bs.exp PV cf' Pq') (tau : TauTrue Bs.exp)
    (e1 : cf' = cf) (e2 : Rw = a.A.row) (e3 : Pq' = Pq) (e4 : HEq hk' n.In.hL) (e5 : eig = n.In.eig) (e6 : θ = n.In.θ)
    (h1 : ∀ i, n.In.Sb ⊆ D.ntw.S0 i) (h2 : ∀ i, OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D))) :
    Nonempty (SeriesState g a n PV Pq) := by
  obtain rfl : kKs = n.kKs := RingHom.ext fun y => Subtype.ext ((hk y).trans (n.hk y).symm)
  subst e1 e2 e3 e5 e6
  cases e4
  exact ⟨{ Bs := Bs, Sb_le := h1, rootsOfUnityRing_le_wittIntegers := h2, lam := ⟨ser.lam, ser.lam_ok, ser.lam_teich, ser.lam_C, ser.lam_q, ser.lam_tie⟩
           YS := YS, eF := eF, fi := fi, ser := ser, tau := tau }⟩

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def PreAt {Z : w.Lt} (z : Dat (w.st Z) w.I P.hX T P.Wt) (Rw : RowSide (w.st Z).toD7)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) → PlE (w.st Z).toD7.host) {α : Type} (h₀ : α)
    (eig : ℕ → (w.st Z).toD7.what₂.FT → ℕ → PlE (w.st Z).toD7.host → ↥(w.st Z).toD7.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.st Z).toD7.host.g kk)) →* (↥(w.st Z).toD7.LL0)ˣ) : Prop :=
  z.R.C = TC.cf w.I w.l Z ∧ ∃ kKs hk hL, HEq hL h₀ ∧
    ∃ (Bs : SideB (w.st Z).toD7 z.R.C Rw (lowAll (w.st Z).toD7) Pq (ratDatR z.R z.cG kKs hk) hL eig θ) (hF : _),
      TauTrue Bs.exp ∧ Nonempty (PreTie (ysOf Bs) z.geo.v₀ Bs.exp hF Pq)

theorem preAt_congr {Z : w.Lt} {z z' : Dat (w.st Z) w.I P.hX T P.Wt} {Rw Rw' Pq Pq'} {α α' : Type} {h₀ : α} {h₀' : α'}
    {eig eig' θ θ'} (e0 : z = z') (e1 : Rw = Rw') (e2 : Pq = Pq') (e3 : HEq h₀ h₀') (e4 : eig = eig') (e5 : θ = θ')
    (h : PreAt (P := P) z Rw Pq h₀ eig θ) : PreAt (P := P) z' Rw' Pq' h₀' eig' θ' := by
  subst e0 e1 e2 e4 e5
  obtain ⟨g1, k, hk, hf, g2, g3⟩ := h
  exact ⟨g1, k, hk, hf, g2.trans e3, g3⟩

theorem preAt_state (hA : GlobalTheory.Published.GlobalArtinReciprocity) {hL : GlobalTheory.Published.LocalLanglandsGL} (hK : K.Over B.toPre)
    (hS : Start K B f T w) (x : St P) (l : LI hL x)
    (hB : ∃ Bs : SideB (Dof x) (cfOf x) l.a.A.row (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig l.rat.In.θ, TauTrue Bs.exp)
    (hSb : ∀ i, l.rat.In.Sb ⊆ (Dof x).ntw.S0 i) (hZ : ∃ Z : GlobalTheory.LamTie.LamDat (Dof x), Z.Ok) :
    PreAt (P := P) x.m.z l.a.A.row l.Pq l.rat.In.hL l.rat.In.eig l.rat.In.θ := by
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.choice_of_local_admissible hL hK hS x l.toLA
  obtain ⟨Bs, hτ⟩ := sideB_tau_congr h4.symm rfl rfl HEq.rfl hB
  exact ⟨h4, l.rat.kKs, l.rat.hk, l.rat.In.hL, HEq.rfl, Bs, x.r.Y.hF, hτ,
    GlobalTheory.T.exists_newThetaData_series_classSums_lattices hA (Dof x) _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG l.rat.kKs l.rat.hk _ _ _ _ _ Bs l.rat.In.Sb x.m.z.geo.v₀ x.r.Y.hF
      x.m.z.pins x.m.intersectionNumber_baseChange (fun j => x.m.z.geo.fw.hv₀ j _) x.m.z.geo.fw.ks l.rat.rat.hecke hSb hτ (h4 ▸ l.a.A.chr) (h4 ▸ l.a.val)
      l.a.elem.split l.Pq_over h1 h2 hZ h3⟩

theorem preAt_copy (hA : GlobalTheory.Published.GlobalArtinReciprocity) {hL : GlobalTheory.Published.LocalLanglandsGL} (hK : K.Over B.toPre)
    (hS : Start K B f T w) (x : St P) (l : LI hL x) (N : TwNew (Dof x))
    (hB : ∃ Bs : SideB N.toD7 (N.cf (cfOf x)) (N.row l.a.A.row) (lowAll (Dof x)) l.Pq (N.rat l.rat.S) l.rat.In.hL l.rat.In.eig
      l.rat.In.θ, TauTrue Bs.exp)
    (hSb : ∀ i, l.rat.In.Sb ⊆ N.tw.S0 i) (hZ : ∃ Z : GlobalTheory.LamTie.LamDat N.toD7, Z.Ok) :
    PreAt (P := P) (datTw x N) ((by with_unfolding_all exact ((N.row l.a.A.row) :))) ((by with_unfolding_all exact (l.Pq :))) l.rat.In.hL ((by with_unfolding_all exact (l.rat.In.eig :))) ((by with_unfolding_all exact (l.rat.In.θ :))) := by
  obtain ⟨x', l', ho, -, hrow, hPq, hS', hSb', hhL, heig, hθ, hR, hcG, hgeo⟩ := GlobalTheory.T.twisted_state_transport_heq_levels hL x l N
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
  have h := preAt_state hA hK hS _ l' (by
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

abbrev kwP : TwNew (DN x N₁) := keepTw (DN x N₁) p.Dat p.th p.lev p.thPsi p.h1 p.thU p.thP p.MtLat p.h2 p.h3 p.nth

def bsP : SideB (DN x (nP p)) (((kwP p).cf cf)) (((kwP p).row Rw)) (lowAll (DN x (nP p))) ((Pq)) (sP p) ((hf)) ((eig))
    ((θ)) :=
  (by with_unfolding_all exact ((keepSideB (DN x N₁) p.Dat p.th p.lev p.thPsi p.h1 p.thU p.thP p.MtLat p.h2 p.h3 p.nth p.hU cf Rw _ Pq _ hf eig θ Bs) :))

theorem series_state_b1_twist {hL : GlobalTheory.Published.LocalLanglandsGL} (hτ : TauTrue Bs.exp) (hC : cf = TC.cf w.I w.l (oTw x N₁).Z)
    (hu : GlobalTheory.UnivChar.IsUnivChar (DN x N₁).nexp) (ho : NoOff (DN x N₁))
    (z : Dat (w.st (oTw x (nP p)).Z) w.I P.hX T P.Wt) (hz : z = datTw x (nP p)) {X0 : BaseLevelRowSide (DN x (nP p))}
    (Y : R3.Read z.R.toRealDat z.F.lv2 X0) (a : StA hL (DN x (nP p)) (TC.cf w.I w.l (oTw x (nP p)).Z) (repOf Y)) (n : InRat Y z.cG)
    (PV : ∀ j : Fin (DN x (nP p)).R.m, principalLevelFrame.RowPsi (Vc (DN x (nP p)) j) (DN x (nP p)).R.nV) {hF'}
    (hPV : ∀ j, GlobalTheory.MtRead.IdFrame hF' (PV j))
    (Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield (DN x (nP p)).host.E)) → PlE (DN x (nP p)).host)
    (hZ : ∃ Z : GlobalTheory.LamTie.LamDat (DN x (nP p)), Z.Ok ∧ Z.Teich ∧ Z.C = TC.cf w.I w.l (oTw x (nP p)).Z ∧
      Z.q0 = AbsolutelyIrreducibleSpan.q0 (DN x (nP p)) ∧ GlobalTheory.LamTie.IsLamTieFull (DN x (nP p)).ntw Z)
    (e2 : HEq a.A.row ((kwP p).row Rw)) (e3 : HEq Pq' Pq) (e4 : HEq n.In.hL hf) (e5 : HEq n.In.eig eig) (e6 : HEq n.In.θ θ)
    (h1 : ∀ i, n.In.Sb ⊆ (DN x (nP p)).ntw.S0 i)
    (h2 : ∀ i, OverSet (DN x (nP p)) ((DN x (nP p)).ntw.S0 i) (insert ((DN x (nP p)).ntw.l i) (lowAll (DN x (nP p))))) :
    Nonempty (SeriesState z.geo a n PV Pq') := by
  subst hz
  obtain ⟨Z, z1, z2, z3, z4, z5⟩ := hZ
  have e1 : ((by with_unfolding_all exact (((kwP p).cf cf) :)) : CharFrame (DN x (nP p))) = TC.cf w.I w.l (oTw x (nP p)).Z := (by with_unfolding_all exact ((congrArg (kwP p).cf hC) :))
  exact nonempty_seriesState _ a n PV (bsP p) (ysP p) ((by with_unfolding_all exact ((Eq.refl Bs.eF) :))) ((by with_unfolding_all exact ((ysOf_fi Bs) :)))
    ((by with_unfolding_all exact ((serP p hu ho Bs.bsup PV hPV Z ⟨z1, z2, z3.trans e1.symm, z4, z5⟩) :))) ((by with_unfolding_all exact (hτ :))) e1 ((by with_unfolding_all exact ((eq_of_heq e2).symm :)))
    ((by with_unfolding_all exact ((eq_of_heq e3).symm :))) ((by with_unfolding_all exact (e4.symm :))) ((by with_unfolding_all exact ((eq_of_heq e5).symm :))) ((by with_unfolding_all exact ((eq_of_heq e6).symm :))) h1 h2

end Install

open GlobalTheory.Mem.Top.GroupRetwisting in

theorem series_copy : PrN → SerN → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}, K.Over B.toPre → Forced K B T → Start K B f T w → ∀ {P : Pre2 K w} (x : St P) (l : SettingsLevel hL x), ∃ N : TwNew (Dof x), (∀ Z : GlobalTheory.LamTie.LamDat (Dof x), GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z) ∧ ∀ (x' : St P) (l' : LI hL x'), x'.o = oTw x N → HEq l'.a.A.row (N.row l.a.A.row) → HEq l'.Pq l.Pq → HEq l'.rat.S (N.rat l.rat.S) → HEq l'.rat.In.Sb l.rat.In.Sb → HEq l'.rat.In.hL l.rat.In.hL → HEq l'.rat.In.eig l.rat.In.eig → HEq l'.rat.In.θ l.rat.In.θ → HEq x'.m.z.R (GlobalTheory.Mem.R3.Tr.real3 (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.R) → HEq x'.m.z.cG x.m.z.cG → HEq x'.m.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.geo) → ∀ m : InMt x'.r.Y (cfOf x') w.I.xi (QOf P), (∀ i, GlobalTheory.MtRead.IdFrame x'.r.Y.hF (m.ad.PV i)) → Nonempty (SeriesState x'.m.z.geo l'.a l'.rat m.ad.PV l'.Pq) := by
  intro hPr _ hL K B f T w hK _ hS P x l
  obtain ⟨-, -, -, -, hr⟩ := GlobalTheory.T.choice_of_local_admissible hL hK hS x l.toLA
  obtain ⟨N, h1, h2, h3, h4, hB⟩ := exists_prepared hPr.what₂.art l.b.Bs l.a.val hr
  obtain ⟨Z, z1, z2, z3, z4, z5⟩ := l.b.lam
  have hSb : ∀ i, l.rat.In.Sb ⊆ N.tw.S0 i := fun i => by
    obtain ⟨i₀, e, -⟩ := h2 i
    rewrite [e]
    exact l.b.Sb_le i₀
  have hS0 : ∀ i, OverSet (Dof x) (N.tw.S0 i) (insert (N.tw.l i) (lowAll (Dof x))) := fun i => by
    obtain ⟨i₀, e, e'⟩ := h2 i
    rewrite [e, e']
    exact l.b.rootsOfUnityRing_le_wittIntegers i₀
  obtain ⟨hC, kKs, hk, hf, g, Bs, hF, hτ, ⟨p⟩⟩ := preAt_copy hPr.what₂.art hK hS x l.toLI N hB hSb
    ⟨_, (lamT_spec N ⟨z1, z2, z3, z4, h1 Z z5⟩).1⟩
  refine ⟨nP p, h1, fun x' l' ho hrow hPq _ hSb' hhL heig hθ hR hcG hgeo m hm => ?_⟩
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at ho
  subst ho
  have e4 : l'.rat.In.Sb = (by with_unfolding_all exact (l.rat.In.Sb :)) := (by with_unfolding_all exact ((eq_of_heq hSb') :))
  exact series_state_b1_twist p hτ hC ((by with_unfolding_all exact (h4 :))) ((by with_unfolding_all exact (h3 :))) m'.z (moved_eq_datTw x _ m' copy' hR hcG hgeo) r'.Y l'.a l'.rat m.ad.PV hm l'.Pq
    ⟨(by with_unfolding_all exact ((lamT (nP p) Z) :)), (by with_unfolding_all exact ((lamT_spec (nP p) ⟨z1, z2, z3, z4, h1 Z z5⟩) :))⟩ ((by with_unfolding_all exact (hrow :))) ((by with_unfolding_all exact (hPq :))) (hhL.trans g.symm) ((by with_unfolding_all exact (heig :))) ((by with_unfolding_all exact (hθ :)))
    (by rewrite [e4]; exact (by with_unfolding_all exact (hSb :))) ((by with_unfolding_all exact (hS0 :)))

end GlobalTheory.HeightCounting.SerCopy

end
