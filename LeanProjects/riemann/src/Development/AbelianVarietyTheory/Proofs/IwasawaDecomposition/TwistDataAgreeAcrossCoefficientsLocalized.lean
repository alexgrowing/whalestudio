import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroIndexPlacesTransferAlongSameFiniteGroup

noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def etaL (x : St P) (L : LocAll (lay0 (Dof x))) : ℕ → B.places.Pl → ℚ := L.lay.fixZ.eta

theorem etaL_nonneg (x : St P) (L : LocAll (lay0 (Dof x))) : ∀ j v, 0 ≤ etaL x L j v := L.lay.fixZ.eta_nonneg

def nL (x : St P) (L : LocAll (lay0 (Dof x))) : NStage B w.C (P.q.W (etaL x L) (etaL_nonneg x L)) where
  loc := ((withLoc L).loc)
  locA := ((withLoc L).locA)
  locT := ((withLoc L).locT)
  nd := ((withLoc L).nd)
  ntw := ((withLoc L).ntw)
  naut := ((withLoc L).naut)
  nbc := ((withLoc L).nbc)
  nexp := ((withLoc L).nexp)
  ntypes := ((withLoc L).ntypes)
  nStage_trivialCharacter_compat := ((withLoc L).nStage_trivialCharacter_compat)
  nStage_trivialCharacter_coeff_eq := ((withLoc L).nStage_trivialCharacter_coeff_eq)
  nth := ((withLoc L).nth)
  nbr := ((withLoc L).nbr)
  nbr_ind := ((withLoc L).nbr_ind)
  self_good := ((withLoc L).self_good)
  ntwbr := ((withLoc L).ntwbr)
  ntwbr_ind := ((withLoc L).ntwbr_ind)
  loc_tie := ((withLoc L).loc_tie)
  bc_tie := ((withLoc L).bc_tie)
  rbar_tie := ((withLoc L).rbar_tie)
  mtpar_tie := ((withLoc L).mtpar_tie)
  Z_tie := ((withLoc L).Z_tie)
  Zgood_tie := ((withLoc L).Zgood_tie)
  etaJ_tie := ((withLoc L).etaJ_tie)

def oL (x : St P) (L : LocAll (lay0 (Dof x))) : P.q.Over :=
  ⟨etaL x L, etaL_nonneg x L, { x.o.V with }, { x.o.S with }, nL x L, x.o.G⟩

abbrev DL (x : St P) (L : LocAll (lay0 (Dof x))) : D7 := (w.st (oL x L).Z).toD7

theorem DL_eq (x : St P) (L : LocAll (lay0 (Dof x))) : DL x L = withLoc L := (Eq.refl (withLoc L))

def sameL (x : St P) (L : LocAll (lay0 (Dof x))) : SameGrp (B := B) (C := w.C) x.o.Z (oL x L).Z where
  e k := (Equiv.refl ((Dof x).nd.PlG k))
  pl k v := (Eq.refl ((Dof x).naut.plGw k v))
  e0 g := (Eq.refl ((Dof x).ntypes.e0.coeff g))

def datL (x : St P) (L : LocAll (lay0 (Dof x))) : Dat (w.st (oL x L).Z) w.I P.hX T P.Wt :=
  Dat.transfer (B := B) (C := w.C) (a := x.o.Z) (b := (oL x L).Z) (sameL x L) x.m.z

theorem datL_cG (x : St P) (L : LocAll (lay0 (Dof x))) : HEq (datL x L).cG x.m.z.cG := (HEq.refl x.m.z.cG)
theorem cf_eq (x : St P) (L : LocAll (lay0 (Dof x))) : HEq (TC.cf w.I w.l (oL x L).Z) (cfL L (cfOf x)) := (HEq.refl (cfL L (cfOf x)))

variable {x : St P} (L : LocAll (lay0 (Dof x)))

abbrev YT (x : St P) (L : LocAll (lay0 (Dof x))) (p0 : BaseLevelRowSide (w.D (oL x L).Z)) : Type 1 :=
  Read (datL x L).R.toRealDat (datL x L).F.lv2 p0

structure YRel {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) : Prop where
  rep : HEq (repOf Y) (repOf x.r.Y)
  eW : ∀ i y, HEq (Y.mj.eW i y) (x.r.Y.mj.eW ((i)) ((y)))
  jMt : ∀ μ h i y, HEq (Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt ((μ)) ((h)) ((i)) ((y))).1

def kKsL (n : InRat x.r.Y x.m.z.cG) : (datL x L).core.Q.c.F →+* ↥(DL x L).LL0 := (n.kKs)

theorem hkL (n : InRat x.r.Y x.m.z.cG) : ∀ y : (datL x L).core.Q.c.F,
    ((kKsL L n y : ↥(DL x L).LL0) : (DL x L).what₂.LL) = algebraMap (datL x L).core.Q.c.F (DL x L).what₂.LL y := (n.hk)

abbrev SL (n : InRat x.r.Y x.m.z.cG) : RatDat (DL x L).ntw := ratDatR (datL x L).R (datL x L).cG (kKsL L n) (hkL L n)

theorem SL_heq (n : InRat x.r.Y x.m.z.cG) : HEq (ratL L n.S) (SL L n) := (HEq.refl (SL L n))

variable (l : LC hL x)

def ysL : NExpRealS (datL x L).R (datL x L).cG (SL L l.rat) where
  fi := (l.b.YS.fi)
  geq := (l.b.YS.geq)
  rho := (l.b.YS.rho)
  chi := (l.b.YS.chi)
  eF := kc% l.b.YS.eF
  bsup := kc% l.b.YS.bsup
  act := kc% l.b.YS.act

def hkH : NExpRealH x.m.z.R x.m.z.cG l.rat.S l.b.YS where
  hL := l.rat.In.hL
  hs := l.b.Bs.hs
  cHk := fun i b k Q => algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)) (l.b.Bs.cHk i b Q) ^ k
  cHk_zero := fun i b Q => pow_zero _
  cHk_unit := fun i b Q =>
    ((l.b.Bs.cHk i b Q).isUnit.map (algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)))).pow 1
  cHk_pow := fun i b k Q => by simp only [pow_one]
  hkEq := by rw [l.b.eF]; exact l.b.Bs.hkEq

def hkHL : NExpRealH (datL x L).R (datL x L).cG (SL L l.rat) (ysL L l) where
  hL := ((hkH l).hL)
  hs := ((hkH l).hs)
  cHk := ((hkH l).cHk)
  cHk_zero := ((hkH l).cHk_zero)
  cHk_unit := ((hkH l).cHk_unit)
  cHk_pow := ((hkH l).cHk_pow)
  hkEq := kc% (hkH l).hkEq

def pvL : ∀ i : Fin (DL x L).R.m, principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (DL x L) i) (DL x L).R.nV :=
  fun i => (by with_unfolding_all exact ((rowPsi (a := x.o.Z) (oL x L).Z (l.mt.ad.PV ((i)))) : _))

abbrev cfD (x : St P) (L : LocAll (lay0 (Dof x))) : CharFrame (DL x L) := TC.cf w.I w.l (oL x L).Z

def chD : NChoice (DL x L) := (chL L l.c.ch)

def tpD : TupTied (DL x L) (cfD x L) (chD L l) := (tpL L l.c.tp)

def mtD : MtFam (DL x L) := (mtL L l.mt.M)

def expD (X : NExpTied (withLoc L)) : NExpTied (DL x L) := (X)

def pqD : HeightOneSpectrum (𝓞 (maximalRealSubfield (DL x L).host.E)) → PlE (DL x L).host := (l.Pq)

def eigD : ℕ → (DL x L).what₂.FT → ℕ → PlE (DL x L).host → ↥(DL x L).LL0 := (l.rat.In.eig)

def sbD : Finset (PlE (DL x L).host) := (l.rat.In.Sb)

theorem fitsL : (oL x L).Fits :=
  ⟨⟨(x.fits.div.left), fun _ _ G => kc% (x.fits.div.2 x.o.S x.o.N G)⟩,
    ⟨(x.fits.grp.pl), (x.fits.grp.teich), (x.fits.grp.chi), (x.fits.grp.ser)⟩,
    ⟨(x.fits.grpAt.pl), (x.fits.grpAt.idem), (x.fits.grpAt.cen)⟩,
    fun eR h => ⟨((x.fits.cen eR h).amb), ((x.fits.cen eR h).mt)⟩⟩

theorem bkL : BkLaw (w.D (oL x L).Z) := (x.bk)

theorem okL : ∀ v, TwistedAt (DL x L) v → IntegralHeckeForms.TwOK ((chD L l).twI v) ((chD L l).k' v) ((chD L l).Q v)
    (((chD L l).psi' v).comp ((DL x L).ntw.art ((chD L l).twI v) ((chD L l).Q v))) := (l.c.ok)

theorem geoL : Nonempty (GlobalTheory.GeoTie.ThetaTie (ysL L l) (datL x L).geo.fw (DL x L).nth) := by
  obtain ⟨g⟩ := l.b.geo
  exact ⟨⟨fun i j b => ⟨((g.side i j b).pt), ((g.side i j b).cover),
    ((g.side i j b).ev_eq), kc% (g.side (kc% i) (kc% j) b).fmUr, (by with_unfolding_all exact ((g.side ((i)) ((j)) b).hk : _)),
    ((g.side i j b).hk_none)⟩, (g.isUnramified₂)⟩⟩

theorem sameGaloisL : GlobalTheory.TwistChoice.SameGalois (Dof x).nd (DL x L).nd :=
  ⟨(Eq.refl (Dof x).R), (HEq.refl (Dof x).host), (Eq.refl (Dof x).loc),
    (HEq.refl (Dof x).nd.Om), (HEq.refl (Dof x).nd.instOm),
    (HEq.refl (Dof x).nd.algOm), (HEq.refl (Dof x).nd.plOm),
    (HEq.refl (Dof x).nd.PlG)⟩

theorem twistDataAgreeAcrossCoefficients_localized : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients (Dof x).ntw (DL x L).ntw :=
  ⟨(HEq.refl (Dof x).ntw.cc), (HEq.refl (Dof x).ntw.Tw), (HEq.refl (Dof x).ntw.l),
    (HEq.refl (Dof x).ntw.O0), (HEq.refl (Dof x).ntw.crO0), (HEq.refl (Dof x).ntw.algO0),
    (HEq.refl (Dof x).ntw.topO0), (HEq.refl (Dof x).ntw.O), (HEq.refl (Dof x).ntw.crO),
    (HEq.refl (Dof x).ntw.algO), (HEq.refl (Dof x).ntw.Ok), (HEq.refl (Dof x).ntw.crOk),
    (HEq.refl (Dof x).ntw.algOk), (HEq.refl (Dof x).ntw.zk), (HEq.refl (Dof x).ntw.pD),
    (HEq.refl (Dof x).ntw.chi1), (HEq.refl (Dof x).ntw.Sig), (HEq.refl (Dof x).ntw.finSig),
    (HEq.refl (Dof x).ntw.jS), (HEq.refl (Dof x).ntw.side), (HEq.refl (Dof x).ntw.rhoS),
    (HEq.refl (Dof x).ntw.S0), (HEq.refl (Dof x).ntw.hEig), (HEq.refl (Dof x).ntw.abelian₂),
    (HEq.refl (Dof x).ntw.sideL), (HEq.refl (Dof x).ntw.RCG), (HEq.refl (Dof x).ntw.grpRCG),
    (HEq.refl (Dof x).ntw.finRCG), (HEq.refl (Dof x).ntw.art), (HEq.refl (Dof x).ntw.th)⟩

theorem sameFormsL : GlobalTheory.TwistChoice.SameForms (Dof x).nexp (DL x L).nexp :=
  ⟨(HEq.refl (Dof x).nexp.Fm), (HEq.refl (Dof x).nexp.acgFm), (HEq.refl (Dof x).nexp.modFmK),
    (HEq.refl (Dof x).nexp.modFmO), (HEq.refl (Dof x).nexp.actG), (HEq.refl (Dof x).nexp.U),
    (HEq.refl (Dof x).nexp.psiU), (HEq.refl (Dof x).nexp.eAlg), (HEq.refl (Dof x).nexp.Dat),
    (HEq.refl (Dof x).nexp.th), (HEq.refl (Dof x).nexp.lev), (HEq.refl (Dof x).nexp.thPsi),
    (HEq.refl (Dof x).nexp.MtV), (HEq.refl (Dof x).nexp.acgMt), (HEq.refl (Dof x).nexp.modMtK),
    (HEq.refl (Dof x).nexp.modMtO), (HEq.refl (Dof x).nexp.MtLat), (HEq.refl (Dof x).nexp.thP),
    (HEq.refl (Dof x).nexp.hkF)⟩

theorem keptL : Kept l.c.ch (chD L l) :=
  ⟨sameGaloisL L, twistDataAgreeAcrossCoefficients_localized L, sameFormsL L, (HEq.refl (Dof x).ntwbr), (HEq.refl l.c.ch.twI), (HEq.refl l.c.ch.sd),
    (HEq.refl l.c.ch.Q), (HEq.refl l.c.ch.k'), (HEq.refl l.c.ch.psi')⟩

def xdD (xd : ThData (Dof x)) : ThData (DL x L) := ⟨(xd.xd0), (xd.thetaBase_invariant_action)⟩

theorem xdD_all {xd : ThData (Dof x)} (h : XdAll xd) : XdAll (xdD L xd) := (h)

theorem ysL_fi : ∀ i y, HEq (((ysL L l).fi i).e y) y := (l.b.fi)

end GlobalTheory.HeightCounting.Fin3

end
