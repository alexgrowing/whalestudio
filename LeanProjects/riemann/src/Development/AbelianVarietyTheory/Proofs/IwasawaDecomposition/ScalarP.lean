import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumEq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3.Tr
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.SerCopy

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

abbrev DN (x : St P) (N : TwNew (Dof x)) : D7 := (w.st (oTw x N).Z).toD7

def oth (x : St P) (N : TwNew (Dof x)) : Oth (B := B) (C := w.C) (P.q.W x.o.η x.o.hη) := ⟨x.o.V, x.o.S, nTw x N, x.o.G⟩

variable {x : St P}

def baN {N : TwNew (Dof x)} (N' : TwNew (Dof x)) {j : Fin (DN x N).R.m} (X : ExportSeries.Base (Vc (DN x N) j) (Wc (DN x N) j)) :
    ExportSeries.Base (Vc (DN x N') ((j))) (Wc (DN x N') ((j))) :=
  (@baT B (@ColW.C B f T w) (@RowPk.Over.Z B f T w (@Pre2.Z₀ B f T K w P) (@Pre2.hX B f T K w P) (@Pre2.Wt B f T K w P) (@Pre2.z B f T K w P) (@Pre2.q B f T K w P) (@oTw K B f T w P x N)) (@RowPk.Over.Z B f T w (@Pre2.Z₀ B f T K w P) (@Pre2.hX B f T K w P) (@Pre2.Wt B f T K w P) (@Pre2.z B f T K w P) (@Pre2.q B f T K w P) (@oTw K B f T w P x N')) (Vc (@DN K B f T w P x N) j) (Wc (@DN K B f T w P x N) j) X)

theorem isNormN {N : TwNew (Dof x)} (N' : TwNew (Dof x)) {j : Fin (DN x N).R.m}
    {X : ExportSeries.Base (Vc (DN x N) j) (Wc (DN x N) j)} {ν : ℂ} (h : IsNorm (datTw x N).R (datTw x N).geo.v₀ X ν) :
    IsNorm (datTw x N').R (datTw x N').geo.v₀ (j := (j)) (@baN K B f T w P x N N' j X) ν := by
  obtain ⟨h0, c, ⟨g, c0R, c0L, hF, u, hu, hh⟩, hn⟩ := h
  exact ⟨h0, c, ⟨(g), (c0R), (c0L),
    kc% (famTie_imp (a := (oTw x N).Z) (oTw x N').Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF), (u), (hu), (hh)⟩, (hn)⟩

variable {N₁ : TwNew (Dof x)} {kKs : (datTw x N₁).core.Q.c.F →+* ↥(DN x N₁).LL0}
  {hk : ∀ y, ((kKs y : ↥(DN x N₁).LL0) : (DN x N₁).what₂.LL) = algebraMap (datTw x N₁).core.Q.c.F (DN x N₁).what₂.LL y}
  {YS : NExpRealS (datTw x N₁).R (datTw x N₁).cG (ratDatR (datTw x N₁).R (datTw x N₁).cG kKs hk)} {X : NExpTied (DN x N₁)} {hF Pq}
  (p : PreTie YS (datTw x N₁).geo.v₀ X hF Pq)

def nP : TwNew (Dof x) := ⟨N₁.tw, (p.ex), N₁.h0, (p.nth), N₁.br, N₁.hbr⟩

def kP : (datTw x (nP p)).core.Q.c.F →+* ↥(DN x (nP p)).LL0 := (kKs)

theorem hkP : ∀ y, ((kP p y : ↥(DN x (nP p)).LL0) : (DN x (nP p)).what₂.LL) =
    algebraMap (datTw x (nP p)).core.Q.c.F (DN x (nP p)).what₂.LL y := (hk)

abbrev sP : RatDat (DN x (nP p)).ntw := ratDatR (datTw x (nP p)).R (datTw x (nP p)).cG (kP p) (hkP p)

def ysP : NExpRealS (datTw x (nP p)).R (datTw x (nP p)).cG (sP p) where
  fi := (YS.fi)
  geq := (YS.geq)
  rho := (YS.rho)
  chi := (YS.chi)
  eF := (YS.eF)
  bsup := (YS.bsup)
  act := (YS.act)

def rhoP : Setup (DN x (nP p)).ntw :=
  (by with_unfolding_all exact ((@seT B w.C _ (oth x N₁) (oth x (nP p)) (((DN x N₁).nd)) (((DN x N₁).ntw)) ((p.ρ))) : _))

theorem goodP : (rhoP p).Good :=
  (by with_unfolding_all exact ((@seGood B w.C _ (oth x N₁) (oth x (nP p)) (((DN x N₁).nd)) (((DN x N₁).ntw)) ((p.ρ)) ((p.good))) : _))

theorem pinP : RealPin (datTw x (nP p)).R (datTw x (nP p)).cG (rhoP p) :=
  ⟨(p.pin.psi), (p.pin.inf), (p.pin.cartT), (p.pin.onbS), (p.pin.onbT), (p.pin.latS), (p.pin.latT), (p.pin.frS),
    (p.pin.frT), (p.pin.vac), (p.pin.Pg), (p.pin.grp), (p.pin.mu0), (p.pin.eta), (p.pin.delta), (p.pin.deltaPl),
    (p.pin.ap), (p.pin.am)⟩

theorem ratP (i : (DN x N₁).ntw.Tw) (j : Fin (DN x N₁).R.m) (b : Bool) (ν : ℂ) :
    SeriesTie.Rat (goodP p) (realRd (ysP p) (datTw x (nP p)).geo.v₀ (goodP p) ((i)) ((j)) b ν) ↔
      SeriesTie.Rat p.good (realRd YS (datTw x N₁).geo.v₀ p.good i j b ν) :=
  ⟨fun h => (by with_unfolding_all exact ((@ratT' B w.C _ (oth x N₁) (oth x (nP p)) (((DN x N₁).nd)) (((DN x N₁).ntw)) ((p.ρ)) ((i)) ((j)) b
      ((p.ex)) (((realRd YS (datTw x N₁).geo.v₀ p.good i j b ν))) ((p.good)) ((h))) : _)),
    fun h => (by with_unfolding_all exact ((@ratT B w.C _ (oth x N₁) (oth x (nP p)) (((DN x N₁).nd)) (((DN x N₁).ntw)) ((p.ρ)) ((i)) ((j)) b
      ((p.ex)) (((realRd YS (datTw x N₁).geo.v₀ p.good i j b ν))) ((p.good)) ((h))) : _))⟩

theorem normP (i : (DN x N₁).ntw.Tw) (j : Fin (DN x N₁).R.m) (b : Bool) (ν : ℂ) :
    IsNorm (datTw x (nP p)).R (datTw x (nP p)).geo.v₀ ((rhoP p).B ((i)) ((j)) b) ν ↔
      IsNorm (datTw x N₁).R (datTw x N₁).geo.v₀ (p.ρ.B i j b) ν :=
  ⟨fun h => (@isNormN K B f T w P x (@nP K B f T w P x N₁ kKs hk YS X hF Pq p) N₁ j (@Setup.B (@DN K B f T w P x (@nP K B f T w P x N₁ kKs hk YS X hF Pq p)) (@DN K B f T w P x (@nP K B f T w P x N₁ kKs hk YS X hF Pq p)).nd (@DN K B f T w P x (@nP K B f T w P x N₁ kKs hk YS X hF Pq p)).ntw (@rhoP K B f T w P x N₁ kKs hk YS X hF Pq p) i j b) ν h), fun h => (by with_unfolding_all exact ((isNormN (nP p) h) :))⟩

theorem scalarP (i : (DN x N₁).ntw.Tw) (j : Fin (DN x N₁).R.m) (b : Bool) :
    IsScalar (ysP p) (datTw x (nP p)).geo.v₀ (goodP p) ((i)) ((j)) b (p.ν i j b) :=
  ⟨(p.scalar i j b).ne, fun h => (normP p i j b _).2 ((p.scalar i j b).norm (h.imp fun ν => (normP p i j b ν).1)),
    fun h => (ratP p i j b _).2 ((p.scalar i j b).rat (h.imp fun ν h' => ⟨(normP p i j b ν).1 h'.1, (ratP p i j b ν).1 h'.2⟩))⟩

def exP (hu : GlobalTheory.UnivChar.IsUnivChar (DN x N₁).nexp) : ExportTie (ysP p) (datTw x (nP p)).geo.v₀ where
  ρ := rhoP p
  good := goodP p
  pin := pinP p
  vec := (p.vec)
  ν := (p.ν)
  scalar := fun i j b => (scalarP p i j b)
  tie := fun i j b => (by with_unfolding_all exact ((@cellT B w.C _ (oth x N₁) (oth x (nP p)) (((DN x N₁).nd)) (((DN x N₁).ntw)) ((p.ρ)) ((i)) ((j)) b
      ((p.ex)) (((realRd YS (datTw x N₁).geo.v₀ p.good ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (p.ν ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b)))) ((p.good))
      (((p.tie ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b)))) : _))
  hecke := fun i j b => (by with_unfolding_all exact ((@heckeTieT B w.C _ (oth x N₁) (oth x (nP p)) (((DN x N₁).nd)) (((DN x N₁).ntw)) ((p.ρ)) ((i))
      ((j)) b ((p.ex)) (((realRd YS (datTw x N₁).geo.v₀ p.good ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (p.ν ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b))))
      (((p.hecke ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b)))) : _))
  univ := (hu)

def expP : NExpTied (DN x (nP p)) :=
  (keepExp (DN x N₁) p.Dat p.th p.lev p.thPsi p.h1 p.thU p.thP p.MtLat p.h2 p.h3 p.nth (PreTie.hU p) X)

def pvP (PV : ∀ j : Fin (DN x (nP p)).R.m, principalLevelFrame.RowPsi (Vc (DN x (nP p)) j) (DN x (nP p)).R.nV) (j : Fin (DN x N₁).R.m) :
    principalLevelFrame.RowPsi (Vc (DN x N₁) j) (DN x N₁).R.nV :=
  ⟨((PV j).ψ), ((PV j).inj), ((PV j).into), ((PV j).onto)⟩

def serP (hu : GlobalTheory.UnivChar.IsUnivChar (DN x N₁).nexp) (ho : NoOff (DN x N₁))
    (hs : ∀ i j b h1 h2 (y : (DN x N₁).nexp.Fm i j b), y ∈ (DN x N₁).nexp.Bsup i j b ↔
      YS.eF i j b h1 h2 y ∈ Bsup (ratDatR (datTw x N₁).R (datTw x N₁).cG kKs hk) i j b)
    (PV : ∀ j : Fin (DN x (nP p)).R.m, principalLevelFrame.RowPsi (Vc (DN x (nP p)) j) (DN x (nP p)).R.nV) {hF'}
    (hPV : ∀ j, GlobalTheory.MtRead.IdFrame hF' (PV j)) {cf : CharFrame (DN x (nP p))} (Z : GlobalTheory.LamTie.LamDat (DN x (nP p)))
    (hZ : Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 (DN x (nP p)) ∧ GlobalTheory.LamTie.IsLamTieFull (DN x (nP p)).ntw Z) :
    SerAt (ysP p) (datTw x (nP p)).geo.v₀ (expP p) PV cf ((Pq)) where
  ex := exP p hu
  bad := (p.bad)
  ch := (p.ch)
  join := (p.join (pvP p PV) fun j ↦ hPV j)
  sup := (hs)
  off := (ho)
  lam := Z
  lam_ok := hZ.1
  lam_teich := hZ.2.1
  lam_C := hZ.2.2.1
  lam_q := hZ.2.2.2.1
  lam_tie := hZ.2.2.2.2

end GlobalTheory.HeightCounting.SerCopy

end
