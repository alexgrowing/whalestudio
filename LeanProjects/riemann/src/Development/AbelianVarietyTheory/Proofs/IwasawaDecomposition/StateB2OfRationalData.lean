import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedThTw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataLaterStagesWithNewTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedReadingTransportedNewTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicSideTransfer
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinTypRepCast
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

section Gen
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F}
  {F : Face3 D A3} {X0 : BaseLevelRowSide D} {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {cf : CharFrame D}
  {g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1}

theorem state_b2_of_rational_data {a : StA hL D cf (repOf Y)} {n : InRat Y cG} {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host}
    (row : RowSide D) (S : RatDat D.ntw) (hLS : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (Sb : Finset (PlE D.host)) (PV' : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
    (hrow : HEq a.A.row row) (hS : HEq n.S S) (hhL : HEq n.In.hL hLS) (heig : HEq n.In.eig eig) (hθ : HEq n.In.θ θ)
    (hSb : HEq n.In.Sb Sb) (hPV : PV = PV') (hPq : HEq Pq Pq')
    (Bs : SideB D cf row (lowAll D) Pq' S hLS eig θ) (Sb_le : ∀ i, Sb ⊆ D.ntw.S0 i)
    (rootsOfUnityRing_le_wittIntegers : ∀ i, OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D)))
    (lam : ∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z)
    (YS : NExpRealS R cG S) (eF : YS.eF = Bs.eF) (fi : ∀ i x, HEq ((YS.fi i).e x) x)
    (ser : SerAt YS g.v₀ Bs.exp PV' cf Pq') (tau : TauTrue Bs.exp)
    (geo : Nonempty (GlobalTheory.GeoTie.ThetaTie YS g.fw D.nth)) : Nonempty (ModuliPointsState g a n PV Pq) := by
  cases eq_of_heq hrow
  cases eq_of_heq hS
  cases eq_of_heq hhL
  cases eq_of_heq heig
  cases eq_of_heq hθ
  cases eq_of_heq hSb
  cases hPV
  cases eq_of_heq hPq
  exact ⟨⟨⟨⟨Bs, Sb_le, rootsOfUnityRing_le_wittIntegers, lam⟩, YS, eF, fi, ser, tau⟩, geo⟩⟩

end Gen

section Gen2

def bsTw {D : D7} {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ} (Bs : SideB D cf Rw low Pq S hL eig θ)
    (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp) :
    SideB (thTw D th).toD7 ((thTw D th).cf cf) ((thTw D th).row Rw) low Pq ((thTw D th).rat S) hL eig θ :=
  { Bs with
    twF := { Bs.twF with }
    tw := { Bs.tw with }
    chiD := { Bs.chiD with }
    chi := { Bs.chi with }
    exp :=
      { Bs.exp with
        mtV := fun i j b k Q ψ h1 h2 h =>
          letI : AddCommGroup (Bs.exp.Wt i j b) := Bs.exp.acgWt i j b
          letI : Module (FractionRing ((thTw D th).toD7.ntw.O i)) (Bs.exp.Wt i j b) := Bs.exp.modWt i j b
          { Bs.exp.mtV i j b k Q ψ h1 h2 h with } } }

def lamTw {D : D7} (N : TwNew D) (Z : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.LamDat N.toD7 := ⟨N.cf Z.C, Z.q0, Z.w0, Z.c, Z.chi⟩

theorem lam_thTw {D : D7} (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp) {cf : CharFrame D}
    (h : ∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z) :
    ∃ Z : GlobalTheory.LamTie.LamDat (thTw D th).toD7, Z.Ok ∧ Z.Teich ∧ Z.C = (thTw D th).cf cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 (thTw D th).toD7 ∧
      GlobalTheory.LamTie.IsLamTieFull (thTw D th).toD7.ntw Z := by
  obtain ⟨Z, h1, h2, h3, h4, h5⟩ := h
  exact ⟨lamTw (thTw D th) Z, ⟨h1.places, h1.aux, h1.big⟩, h2, congrArg (TwNew.cf (thTw D th)) h3, h4, h5⟩
end Gen2

section MtCopy
variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem mt_thTw (x : St P) (l : LI hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp)
    (m : Moved (oTw x (thTw (Dof x) th))) (hm : m.z = datTw x (thTw (Dof x) th)) (hc : m.Copy) (hh : m.Coh)
    (r : ReadPk m (sideTw x (thTw (Dof x) th))) (hp : r.Pin)
    (hj : ∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1) :
    ∃ mt : InMt r.Y (cfOf (stTw x _ m hc hh r hp)) w.I.xi (QOf P),
      mt.ad.PV = fun i => (by with_unfolding_all exact (rowPsi (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z (l.mt.ad.PV (by with_unfolding_all exact i)) :)) := by
  rcases m with ⟨z⟩
  dsimp only at hm
  subst hm
  refine ⟨{ M := (by with_unfolding_all exact (((thTw (Dof x) th).mt l.mt.M) :))
            ad :=
              { PV := fun i => (by with_unfolding_all exact ((rowPsi (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z (l.mt.ad.PV ((i)))) : _))
                std := (by with_unfolding_all exact (l.mt.ad.std :))
                eW := (by with_unfolding_all exact (l.mt.ad.eW :))
                read := fun μ h i y g => by
                  have e := congrFun (eq_of_heq (hj μ h i y)) ((l.mt.ad.PV i).ψ g)
                  exact Eq.trans ((by with_unfolding_all exact ((l.mt.ad.read μ h i y g) :))) e.symm
                rat := (by with_unfolding_all exact (l.mt.ad.rat :))
                wt := (by with_unfolding_all exact (l.mt.ad.wt :))
                id := (by with_unfolding_all exact (l.mt.ad.id :)) }
            mt := (by with_unfolding_all exact (((twist_settings_unread (Dof x) (cfOf x) l.a.jE l.a.A (thTw (Dof x) th)).2.1 _ _ _ l.mt.mt) :)) }, rfl⟩
end MtCopy

end GlobalTheory.HeightCounting.Up
end
