import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHcParamOfCode
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MPowFiveMulFMulLLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsWeightsInWindows

noncomputable section

namespace GlobalTheory.EX.OB

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.Mem NumberField

@[reducible] def setDiv (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) : D7 :=
  { D with
    div := { D.div with
      Nu := fun u => { D.div.Nu u with L := N u }
      h := h
      HH := max 1 (sFrame (fun u => { D.div.Nu u with L := N u }) h + D.div.RR.muMax)
      HH_ge := le_max_right _ _ } }

def leastOff (M : ℕ) : ℕ := sInf {r | r.Prime ∧ ¬ r ∣ M}

def GamS (C : FC) (s : Scale) (R : Ranks) : ℝ := Real.exp (C.CGam * (R.m : ℝ) ^ 5 * R.f * s.L)

structure ChOK (s : Scale) (C : FC) (cD ch : ℝ) (P : PreCh) (q1 : ℕ) (a b : P.R.A → ℤ)
    (c : P.Word → Fin (P.R.k - 2) → Bool) : Prop where
  rank : RankVal s P.R
  ct2 : P.H.CT2 = C.CT2
  val : HostVal s C.P.Cpde P.H
  arith : HostArith P.H
  thick : P.H.secondSet_card_lower_bound ∧ 4 * P.H.Lw * P.H.T2.card ≤ P.R.n0
  dlog : |dlogH P.H| ≤ s.x ^ s.eps
  gnorm : ∀ i, ∃ π : 𝓞 P.H.E, (π : P.H.E) ∈ P.H.K ∧ (π : P.H.E) * P.H.conj (π : P.H.E) = (P.H.g i : P.H.E) ∧
    (π - 1) ∈ Ideal.span {((P.H.QS * P.H.q * P.H.d : ℕ) : 𝓞 P.H.E)}
  pde : P.H.pde % Nat.lcm 15 (P.H.QS * P.H.q * P.H.d) = 1 ∧ P.H.pde' % Nat.lcm 15 (P.H.QS * P.H.q * P.H.d) = 1
  small : q1 ∈ P.H.levelPrimes ∧ q1 ≠ P.H.pde ∧ q1 ≠ P.H.pde' ∧ (∀ i, q1 ≠ P.H.g i) ∧
    q1 % (leastOff (P.H.QS * P.H.q * P.H.d * (P.H.pde - 1) * (P.H.pde' - 1)) * (P.H.QS * P.H.q * P.H.d)) = 1
  lev : ∀ p ∈ P.H.levelPrimes, (∃ i, p = P.H.g i) ∨ (p : ℝ) < s.X'
  win : WinOK s C.GK P.H a b
  card : Fintype.card P.Word = ⌈3 * GamS C s P.R ^ 2 * s.x ^ C.P.CF⌉₊
  inj : Function.Injective c
  hc : ∀ u, HCVal s cD ch P.H (fun τ : Tau P.R => (τ : P.R.GG)) (P.hcW u) (fun t => b t)
  code : ∀ u τ (l : ℕ) (h : l < P.R.k - 2), (P.hcW u τ).u ⟨l + 1, by omega⟩ =
    (P.hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if c u ⟨l, h⟩ then (Delv s cD : ℚ) else 0)
  top : ∀ u (τ : Tau P.R) (t : P.H.TT) (h : 0 < P.R.k), (τ : P.R.GG) = P.R.tau1 t →
    (P.hcW u τ).u ⟨0, h⟩ = (a t : ℚ) + ((P.R.k : ℚ) - 1) / 2 ∧
      (P.hcW u τ).u ⟨P.R.k - 1, by omega⟩ = -(b t : ℚ) - ((P.R.k : ℚ) - 1) / 2

structure ChGood (s : Scale) (C : FC) (C5 c6 Cb cD ch : ℝ) (P : PreCh) (a b : P.R.A → ℤ)
    (c : P.Word → Fin (P.R.k - 2) → Bool) : Prop where
  ok : ChOK s C cD ch P (DC.q0H P.H) a b c
  host : HostGood s C.P.Cpde C5 c6 Cb P.H (DC.q0H P.H)

def Over (D : D7) (P : PreCh) (Lv : LevCh P) : Prop :=
  ∃ (sp : @Spaces P.R Lv.host.F Lv.host.E _ _ _ _ Lv.host.cmStar _) (hT : _) (hY : _) (hA : _) (hV : _) (hz : _) (X : Stages),
    X.B.toPre = Pre.ofCh P Lv sp hT hY hA hV hz ∧ D = X.toD7

theorem Over.host_heq {D : D7} {P : PreCh} {Lv : LevCh P} (h : Over D P Lv) : D.R = P.R ∧ HEq D.host Lv.host := by
  obtain ⟨sp, hT, hY, hA, hV, hz, X, h1, rfl⟩ := h
  have key : ∀ B : Pre, B = Pre.ofCh P Lv sp hT hY hA hV hz → B.R = P.R ∧ HEq B.host Lv.host := by
    rintro B rfl
    exact ⟨rfl, HEq.rfl⟩
  exact key X.B.toPre h1

theorem Over.field {D : D7} {P : PreCh} {Lv : LevCh P} (h : Over D P Lv) : HEq D.host.toHostAx P.H.toHostAx := by
  have key : ∀ (R : Ranks) (H : Host R), R = P.R → HEq H Lv.host → HEq H.toHostAx P.H.toHostAx := by
    rintro R H rfl hH
    rw [eq_of_heq hH]
  exact key _ _ h.host_heq.1 h.host_heq.2

structure Lay (D : D7) : Type 1 where
  gatT : GatTies D
  ties : Formalism.BasicNotions.Ties D
  X : DivX D
  rrDef : DV.RRDef D
  lev : LevelData D
  th : ThetaX D
  th_io : th.TieIo
  cmp : LatCmp D
  tw : TwForms D
  Gy : G.LatInst D
  vram : cmp.VramDef Gy
  fills_all : FillsAll gatT Gy
  ker : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    LocalToGlobal₂ D gatT cmp tw u w h (Gy.Ch u w h)
  idx : IdxDefs D X
  kap_def : DV.KapDef D
  lam_def : DV.LamDef D
  kapR_def : DV.KapRBase X
  errX : ErrX D
  piG_lev : PiGLevel D lev errX
  piT_lev : PiTLevel D lev errX
  seen : SeenDef D errX
  tauOf : TauOfDef D errX
  dgam : DGamDef D
  nch : NChoice D
  nch_tie : NChTie D nch
  xd : ThData D
  p0 : BaseLevelRowSide D
  rationalRoots_def : p0.s.RRDef
  amb : AmbForm D (RowSide.sharp D)
  amb0 : AmbForm D p0.s
  duStar_def : ∀ u, ((D.mem u).A.duStar : ℝ) = StandardLattice.duStarU D u
  Dstar_def : D.what₂.Dstar = StandardLattice.DstarD D
  gauge : letI := D.host.cmStar; GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig
  gauge_def : letI := D.host.cmStar; gauge.IsGauge

structure RecOK (s : Scale) (C : FC) (cD : ℝ) (D : D7) : Prop where
  del : D.s.Del = (Delv s cD : ℚ)
  etaF : D.div.etaF = 6 * s.x ^ (-C.P.CF)
  untw : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → D.what₂.Aj j w = 0
  fin : {w | D.what₂.muAt w ≠ D.what₂.mu0}.Finite
  dgam : ∀ u, 0 < (D.mem u).C.DGam
  full : ∀ u (x : (D.div.Nu u).V), ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ DV.MramL D u
  tame : ∀ (k : Fin 2) (v : D.nd.PlG k), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    DC.TameDistinct D.R.r (D.host.g k) (D.nd.chiT k v)
  mink : DGamChoice_at D
  atT : ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∃ n : ℕ, n ≠ 0 ∧
    (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧
    ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x)

def WtEq {D : D7} (L : SizeData₂ D) {φ : Formalism.HC.Frame} (a b : φ.A → ℤ) : Prop :=
  ∀ (t : D.host.TT) (t' : φ.A), (t : D.R.A).val = t'.val → L.aT t = a t' ∧ L.bT t = b t'

def LedOK (s : Scale) (C : FC) (cD ch : ℝ) {D : D7} (Y : Lay D) {φ : Formalism.HC.Frame} (a b : φ.A → ℤ) : Prop :=
  ∀ L : SizeData₂ D, L.sc = s → WtEq L a b → Val C cD ch L →
    (∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j ∈ SizeData₂.lifts D, Fval L j w = 0) ∧
    ∀ X : G.Inst D L, CanonInst X → G.EpDef X C.cX.Ce → G.KapIDef X C.GK → (∀ w, G.ParametersFill X C.GK w) →
      G.LatTied Y.gatT X Y.Gy ∧ EpTie X ∧
      ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
        G.VV X C.GK (G.aL L) (G.bL L) (D.what₂.places.resChar w) ≠ ∅ →
        (∀ x, Y.cmp.cmp u w hg (D.nuIn u x) ∈ G.NP X Y.Gy C.GK u w hg → InLoc (D.plEq w) (DV.MramL D u) x) ∧
        ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ DV.MramL D u, Y.cmp.cmp u w hg (D.nuIn u (n • x)) ∈ G.NP X Y.Gy C.GK u w hg

structure LedPart (C : FC) {D : D7} (Y : Lay D) where
  L : SizeData₂ D
  ta : TiesAt C L Y.gatT
  Gy_eq : ta.Gy = Y.Gy
  nuDef : DV.NuDef D L
  lat : LatDefs D L ta.Gx Y.Gy C.GK Y.cmp
  ep_def : G.EpDef ta.Gx C.cX.Ce
  ep_tie : EpTie ta.Gx
  kapI_def : G.KapIDef ta.Gx C.GK
  nu_unserved : NuUnserved ta.Gx C.GK
  err : ErrDefs D L Y.errX Y.lev C.GK C.cX.err
  fdef : L.FDef

structure Obj (D : D7) : Type 1 where
  L : SizeData₂ D
  gatT : GatTies D
  Gx : G.Inst D L
  Gy : G.LatInst D
  K : G.Consts
  X : DivX D
  cX : ExtraC
  ex : Extra D L gatT Gx Gy K X cX

namespace Obj

variable {D : D7} (O : Obj D)

abbrev lev : LevelData D := O.ex.lev

abbrev th : ThetaX D := O.ex.th

abbrev cmp : LatCmp D := O.ex.cmp

abbrev tw : TwForms D := O.ex.tw

abbrev errX : ErrX D := O.ex.errX

abbrev nch : NChoice D := O.ex.nch

abbrev xd : ThData D := O.ex.xd

abbrev p0 : BaseLevelRowSide D := O.ex.p0

end Obj

section Transport

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)

@[reducible] def ledTr (L : SizeData₂ D) : SizeData₂ (setDiv D N h) := { L with }

@[reducible] def instTr {L : SizeData₂ D} (X : G.Inst D L) : G.Inst (setDiv D N h) (ledTr N h L) := { X with }

@[reducible] def gatTr (x : GatTies D) : GatTies (setDiv D N h) := { x with }

@[reducible] def latTr (x : G.LatInst D) : G.LatInst (setDiv D N h) := { x with }

@[reducible] def cmpTr (x : LatCmp D) : LatCmp (setDiv D N h) := { x with }

@[reducible] def twTr (x : TwForms D) : TwForms (setDiv D N h) := { x with }

@[reducible] def thTr (x : ThetaX D) : ThetaX (setDiv D N h) := { x with }

@[reducible] def errTr (x : ErrX D) : ErrX (setDiv D N h) := { x with }

@[reducible] def nchTr (x : NChoice D) : NChoice (setDiv D N h) := { x with }

@[reducible] def xdTr (x : ThData D) : ThData (setDiv D N h) := { x with }
open DivX (md) in

@[reducible] def divTr (X : DivX D) : DivX (setDiv D N h) := { X with md := fun S κ p _ la z => { md X S κ p la z with } }

@[reducible] def sideTr {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) :
    RowSide (setDiv D N h) EE := { S with }

section Side

variable {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)

theorem downTo_tr (μ : D.what₂.Tup) (j : ℕ) : (sideTr N h S).downTo μ j = S.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [RowSide.downTo, RowSide.downTo, ih]

theorem iota_tr (μ : D.what₂.Tup) : (sideTr N h S).iota μ = S.iota μ := by
  unfold RowSide.iota; rw [downTo_tr]

theorem Qsp_tr (μ : D.what₂.Tup) : (sideTr N h S).Qsp μ = S.Qsp μ := by
  unfold RowSide.Qsp RowSide.Usp; rw [iota_tr]; rfl

theorem RRset_tr (μ : D.what₂.Tup) : (sideTr N h S).RRset μ = S.RRset μ := by
  unfold RowSide.RRset RowSide.LamSet; rw [iota_tr]; simp only [Qsp_tr]; rfl

theorem iiStar_tr : (sideTr N h S).iiStar = S.iiStar := by
  have key : ∀ (f f' : S.Amb D.what₂.mu0 →ₗ[ℂ] EE) (Q Q' : Submodule ℂ (S.Amb D.what₂.mu0)), f = f' → Q = Q' →
      f.domRestrict Q ∘ₗ LinearMap.adjoint (f.domRestrict Q) = f'.domRestrict Q' ∘ₗ LinearMap.adjoint (f'.domRestrict Q') := by
    rintro _ _ _ _ rfl rfl; rfl
  exact key _ _ _ _ (iota_tr N h S _) (Qsp_tr N h S _)

theorem kapOf_tr {n : ℕ} (ty : Fin n → D.what₂.FT) : (sideTr N h S).kapOf ty = S.kapOf ty := by
  unfold RowSide.kapOf RowSide.kapRatio; rw [iiStar_tr]; rfl

theorem rrDef_tr (H : S.RRDef) : (sideTr N h S).RRDef := by
  unfold RowSide.RRDef; simp only [RRset_tr]; exact H

end Side

theorem kapSharp_tr : kapSharp (setDiv D N h) = kapSharp D := kapOf_tr N h (RowSide.sharp D) _

section Local

variable {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (a b : G.HH D → ℤ) (p j : ℕ)

theorem VV_tr : G.VV (instTr N h X) K a b p = G.VV X K a b p := by
  have e1 : G.Cand _ (ledTr N h L) K p = G.Cand D L K p := rfl
  have e2 : G.goodReps (instTr N h X) p = G.goodReps X p := rfl
  have e3 : G.Sig (instTr N h X) K a b p = G.Sig X K a b p := rfl
  unfold G.VV; rw [e1, e2, e3]

theorem tau_translate : G.tauP (instTr N h X) K a b p = G.tauP X K a b p := by
  unfold G.tauP; rw [VV_tr]; rfl

theorem ioP_instTr : G.ioP (instTr N h X) K a b p = G.ioP X K a b p := by
  unfold G.ioP; rw [VV_tr]; rfl

theorem gainP_instTr : G.gainP (instTr N h X) K a b p j = G.gainP X K a b p j := by
  unfold G.gainP; rw [VV_tr]; rfl

theorem TTP_tr : G.TTP (instTr N h X) K a b p = G.TTP X K a b p := by
  unfold G.TTP; rw [VV_tr]; rfl

theorem fills_tr (w : D.what₂.places.Pl) (H : G.ParametersFill X K w) : G.ParametersFill (instTr N h X) K w :=
  ⟨H.1, H.2.1, H.2.2.1.trans (TTP_tr N h X K _ _ _).symm,
    fun h1 h2 j hj => (H.2.2.2.1 h1 h2 j hj).trans (gainP_instTr N h X K _ _ _ _).symm,
    H.2.2.2.2.1.trans (tau_translate N h X K _ _ _).symm, H.2.2.2.2.2.1.trans (ioP_instTr N h X K _ _ _).symm, H.2.2.2.2.2.2⟩

theorem NP_tr (Y : G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    G.NP (instTr N h X) (latTr N h Y) K u w hg = G.NP X Y K u w hg := by
  have e0 : G.aL (ledTr N h L) = G.aL L := rfl
  have e1 : G.bL (ledTr N h L) = G.bL L := rfl
  have e2 : ∀ a b p t, G.Sv (instTr N h X) K a b p t = G.Sv X K a b p t := fun _ _ _ _ => rfl
  unfold G.NP
  simp only [e0, e1, e2, VV_tr, tau_translate]
  rfl

end Local

set_option maxHeartbeats 800000 in

theorem bk_tr (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ) (ψ : BlochKatoReduction.Gen.GE D.nd →* (D.ntw.Ok i k)ˣ) :
    BlochKatoReduction.Gen.bk (BlochKatoReduction.bk0 (setDiv D N h)) i s k ψ = BlochKatoReduction.Gen.bk (BlochKatoReduction.bk0 D) i s k ψ := rfl

theorem sLen_tr (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : BlochKatoReduction.Gen.GE D.nd →* (D.ntw.Ok i k)ˣ) :
    BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 (setDiv D N h)) i s k Q ψ = BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) i s k Q ψ := by
  unfold BlochKatoReduction.Gen.sLen BlochKatoReduction.Gen.selT
  rw [bk_tr]
  rfl

theorem twAt_tr {x : NChoice D} {y : ThData D} (H : LocalQuadraticParts.TWAt D x y) : LocalQuadraticParts.TWAt (setDiv D N h) (nchTr N h x) (xdTr N h y) := by
  obtain ⟨hc, N0, S, H⟩ := H
  refine ⟨hc, N0, S, fun w hw => ⟨(H w hw).1, ?_⟩⟩
  obtain ⟨h1, h2, h3, ⟨e, h4, h4', h4''⟩, h5, h6⟩ := (H w hw).2
  exact ⟨h1, h2, h3, ⟨e, h4, h4', fun s hs => (sLen_tr N h _ s _ _ _).trans_le (h4'' s hs)⟩, h5, h6⟩

def extraTr {L : SizeData₂ D} {gatT : GatTies D} {Gx : G.Inst D L} {Gy : G.LatInst D} {K : G.Consts} {X : DivX D} {cX : ExtraC}
    (ex : Extra D L gatT Gx Gy K X cX) :
    Extra (setDiv D N h) (ledTr N h L) (gatTr N h gatT) (instTr N h Gx) (latTr N h Gy) K (divTr N h X) cX where
  lev := ex.lev
  th := thTr N h ex.th
  th_io := ex.th_io
  cmp := cmpTr N h ex.cmp
  lat := ⟨ex.lat.vram, fun u w hg hv x => by
    rw [NP_tr]; exact ex.lat.served u w hg (by rw [← VV_tr N h]; exact hv) x, ex.lat.atT⟩
  tw := twTr N h ex.tw
  ker := fun u w g => { ex.ker u w g with }
  ep_def := ex.ep_def
  ep_tie := ex.ep_tie
  kapI_def := ex.kapI_def
  fills_all := ex.fills_all
  nu_unserved := fun u w h1 h2 => ex.nu_unserved u w h1 (by rw [← VV_tr N h]; exact h2)
  idx := { ex.idx with }
  kap_def := ex.kap_def
  lam_def := ex.lam_def
  kapR_def := ex.kapR_def.trans (kapSharp_tr N h).symm
  errX := errTr N h ex.errX
  err := { ex.err with }
  nch := nchTr N h ex.nch
  nch_tie := { ex.nch_tie with }
  xd := xdTr N h ex.xd
  p0 := ⟨sideTr N h ex.p0.s⟩
  rationalRoots_def := rrDef_tr N h _ ex.rationalRoots_def
  amb := { ex.amb with }
  amb0 := { ex.amb0 with }
  fdef := ex.fdef
  duStar_def := ex.duStar_def
  Dstar_def := ex.Dstar_def
  gauge := ex.gauge
  gauge_def := ex.gauge_def

end Transport

def Obj.tr {D : D7} (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) : Obj (setDiv D N h) :=
  ⟨ledTr N h O.L, gatTr N h O.gatT, instTr N h O.Gx, latTr N h O.Gy, O.K, divTr N h O.X, O.cX, extraTr N h O.ex⟩

def Obj.ofPt {C : FC} (p : Pt C) : Obj p.D := ⟨p.L, p.gatT, p.ta.Gx, p.ta.Gy, C.GK, p.xa.X, C.cX, p.xa.ex⟩

def ptO (QO : ∀ D : D7, Obj D → Prop) : PtProp := fun D L gatT Gx Gy K X cX ex => QO D ⟨L, gatT, Gx, Gy, K, X, cX, ex⟩

def objO (Q : PtProp) : ∀ D : D7, Obj D → Prop := fun D O => Q D O.L O.gatT O.Gx O.Gy O.K O.X O.cX O.ex

theorem ptO_objO (Q : PtProp) : ptO (objO Q) = Q := rfl

theorem objO_ptO (QO : ∀ D : D7, Obj D → Prop) : objO (ptO QO) = QO := rfl

theorem has_ptO {C : FC} (p : Pt C) (QO : ∀ D : D7, Obj D → Prop) : p.Has (ptO QO) ↔ QO p.D (Obj.ofPt p) := Iff.rfl

def LedPart.extra {C : FC} {D : D7} {Y : Lay D} (p : LedPart C Y) : Extra D p.L Y.gatT p.ta.Gx Y.Gy C.GK Y.X C.cX :=
  { Y with
    lat := p.lat, ep_def := p.ep_def, ep_tie := p.ep_tie, kapI_def := p.kapI_def, nu_unserved := p.nu_unserved, err := p.err,
    fdef := p.fdef }

def Lay.obj {C : FC} {D : D7} (Y : Lay D) (p : LedPart C Y) : Obj D := ⟨p.L, Y.gatT, p.ta.Gx, Y.Gy, C.GK, Y.X, C.cX, p.extra⟩

def nPrime {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V :=
  Submodule.span (𝓞 D.what₂.LL) {x | ∃ a ∈ DV.Iu D L u, ∃ y ∈ L.NuLat u, x = (a : D.what₂.LL) • y}

namespace LedPart

variable {C : FC} {D : D7} {Y : Lay D} (p : LedPart C Y)

def ht : D.what₂.Word → ℝ := DV.hExpl6 D p.L Y.X C.Csz

def pt : Pt C where
  D := setDiv D (nPrime p.L) p.ht
  L := ledTr (nPrime p.L) p.ht p.L
  gatT := gatTr (nPrime p.L) p.ht Y.gatT
  ta :=
    { Gx := instTr (nPrime p.L) p.ht p.ta.Gx
      Gy := latTr (nPrime p.L) p.ht Y.Gy
      supp_sat := p.ta.supp_sat
      tw_supp := p.ta.tw_supp
      fills := fun w => fills_tr (D := D) (nPrime p.L) p.ht p.ta.Gx C.GK w (p.ta.fills w)
      lats0 := fun w u h1 h2 => p.ta.lats0 w u (by rw [← VV_tr (nPrime p.L) p.ht]; exact h1) h2
      latTied := (p.Gy_eq ▸ p.ta.latTied : G.LatTied Y.gatT p.ta.Gx Y.Gy)
      drop_iff := p.ta.drop_iff }
  xa :=
    { ties := { Y.ties with }
      X := divTr (nPrime p.L) p.ht Y.X
      nuDef := p.nuDef
      nprimeDef := fun _ => rfl
      rrDef := Y.rrDef
      h_eq := fun _ => rfl
      ex := extraTr (nPrime p.L) p.ht p.extra }

theorem pt_D : p.pt.D = setDiv D (nPrime p.L) p.ht := rfl

theorem pt_sc : p.pt.L.sc = p.L.sc := rfl

theorem ofPt_pt : Obj.ofPt p.pt = (Y.obj p).tr (nPrime p.L) p.ht := rfl

theorem pt_wtEq {φ : Formalism.HC.Frame} {a b : φ.A → ℤ} (H : WtEq p.L a b) : WtEq p.pt.L a b := H

theorem pt_val {cD ch : ℝ} (H : Val C cD ch p.L) : Val C cD ch p.pt.L := { H with }

theorem pt_canon (H : CanonInst p.ta.Gx) : CanonInst p.pt.ta.Gx := H

theorem pt_has {s : Scale} {cD : ℝ} {Q : PtProp} (hR : RecOK s C cD D) (hT : LocalQuadraticParts.TWAt D Y.nch Y.xd) (h0 : DC.GlobalTwistingFacts p.L)
    (hQ : p.pt.Has Q) : p.pt.Has (DC.withObj Q) :=
  ⟨⟨hQ, h0⟩, hR.tame, hR.mink, twAt_tr (nPrime p.L) p.ht hT⟩

end LedPart

def RecEx (QO : ∀ D : D7, Obj D → Prop) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps C8 C5 c6 Cb : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → 1 ≤ C8 → ∃ K0 : TransportedAlt,
    ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ cs x0 : ℝ, 0 < cs ∧
      ∀ (s : Scale) (P : PreCh) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool),
        s.eps = eps → x0 ≤ s.x → ChGood s C C5 c6 Cb cD ch P a b c →
        ∃ (du : P.Word → ℕ) (Ds : ℝ), (∀ u, 0 < du u) ∧ 0 < Ds ∧
          (∀ u, cs * P.R.m * s.L ≤ Real.log ((Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) *
            GamS C s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k)))) ∧
          ∀ Lv : LevCh P, Lv.duStar = du → Lv.Dstar = Ds → Lv.GamP = GamS C s P.R →
            ∃ (D : D7) (Y : Lay D), Over D P Lv ∧ RecOK s C cD D ∧ LedOK s C cD ch Y a b ∧ LocalQuadraticParts.TWAt D Y.nch Y.xd ∧
              ∀ p : LedPart C Y, p.L.sc = s → WtEq p.L a b → Val C cD ch p.L → CanonInst p.ta.Gx →
                QO p.pt.D (Obj.ofPt p.pt)

theorem RecEx.imp {QO QO' : ∀ D : D7, Obj D → Prop} (h : RecEx QO) (hQ : ∀ D O, QO D O → QO' D O) : RecEx QO' := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨cs, x0, hcs, h⟩ := h ch hch
  refine ⟨cs, x0, hcs, fun s P a b c d1 d2 d3 => ?_⟩
  obtain ⟨du, Ds, e1, e2, e3, h⟩ := h s P a b c d1 d2 d3
  refine ⟨du, Ds, e1, e2, e3, fun Lv f1 f2 f3 => ?_⟩
  obtain ⟨D, Y, g1, g2, g3, g4, g5⟩ := h Lv f1 f2 f3
  exact ⟨D, Y, g1, g2, g3, g4, fun p k1 k2 k3 k4 => hQ _ _ (g5 p k1 k2 k3 k4)⟩

def Lay.ofPt {C : FC} (p : Pt C) : Lay p.D :=
  { p.xa.ex with
    gatT := p.gatT, ties := p.xa.ties, X := p.xa.X, rrDef := p.xa.rrDef, Gy := p.ta.Gy, vram := p.xa.ex.lat.vram,
    piG_lev := p.xa.ex.err.piG_lev, piT_lev := p.xa.ex.err.piT_lev, seen := p.xa.ex.err.seen, tauOf := p.xa.ex.err.tauOf,
    dgam := p.xa.ex.err.dgam }

def LedPart.ofPt {C : FC} (p : Pt C) : LedPart C (Lay.ofPt p) :=
  { p.xa.ex with L := p.L, ta := p.ta, Gy_eq := rfl, nuDef := p.xa.nuDef }

theorem obj_ofPt {C : FC} (p : Pt C) : (Lay.ofPt p).obj (LedPart.ofPt p) = Obj.ofPt p := rfl

theorem pt_ofPt {C : FC} (p : Pt C) :
    (LedPart.ofPt p).pt.D.div.Nu = p.D.div.Nu ∧ (LedPart.ofPt p).pt.D.div.h = p.D.div.h := by
  refine ⟨funext fun u => ?_, funext fun u => (p.xa.h_eq u).symm⟩
  show ({ p.D.div.Nu u with L := nPrime p.L u } : HLat _) = p.D.div.Nu u
  rw [show nPrime p.L u = (p.D.div.Nu u).L from (p.xa.nprimeDef u).symm]

theorem nonempty_ledPart_iff (C : FC) : (∃ (D : D7) (Y : Lay D), Nonempty (LedPart C Y)) ↔ Nonempty (Pt C) :=
  ⟨fun ⟨_, _, ⟨p⟩⟩ => ⟨p.pt⟩, fun ⟨p⟩ => ⟨_, _, ⟨LedPart.ofPt p⟩⟩⟩

theorem leastOff_eq_rPrH {R : Ranks} (H : Host R) (hc : H.ccK = ⊤) :
    leastOff (H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1)) = DC.rPrH H := by
  unfold DC.rPrH leastOff
  rw [hc, Ideal.absNorm_top, mul_one]

@[reducible] def setUnipotentTranslate {R : Ranks} (H : Host R) (u0 : ℕ) : Host R := { H with u0 := R.ofNat u0 }

theorem chGood_of_host (eps C5 c6 Cb cD ch : ℝ) (C : FC) (he : 0 < eps) (he1 : eps < 1 / 52) (hC : Std C) (hcD : 0 ≤ cD)
    (hch : 402 ≤ ch) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ)
      (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → H.CT2 = C.CT2 →
      HostGood s C.P.Cpde C5 c6 Cb H (DC.q0H H) → WinOK s C.GK H a b → M = ⌈3 * GamS C s R ^ 2 * s.x ^ C.P.CF⌉₊ →
      Function.Injective c → ∃ (hcW : Fin M → Tau R → HCParam R) (w0 : Fin M) (h1 : _) (h2 : _) (h3 : _) (h4 : _) (h5 : _)
        (h6 : _) (h7 : _) (h8 : _),
        ChGood s C C5 c6 Cb cD ch (@PreCh.mk R (setUnipotentTranslate H u0) h1 h2 h3 (Fin M) _ w0 hcW h4 h5 h6 h7 h8) a b c := by
  have h8 : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨x1, hx1⟩ := small_prime_lt eps _ he h8
  obtain ⟨x3, hx3⟩ := exists_hc_family eps cD ch C.P.Cpde he he1 hcD hch
  refine ⟨max x1 x3, fun s R H a b M c u0 hs hx hR hT hH hW hM hc => ?_⟩
  simp only [max_le_iff] at hx
  have hH' : HostGood s C.P.Cpde C5 c6 Cb (setUnipotentTranslate H u0) (DC.q0H (setUnipotentTranslate H u0)) := hH
  obtain ⟨hv, har, hT2, hT3, -, -, hdl, -, -, hBB, hgn, hpde, ⟨hp0, hmod0, hq0le, hq1, hq2⟩, hlev⟩ := hH
  have hN2 : 2 ≤ H.QS * H.q * H.d := by
    have h1 : 0 < H.QS * H.q := Nat.mul_pos H.QS_pos H.hyp.1.pos
    exact H.hyp.2.1.two_le.trans (Nat.le_mul_of_pos_left _ h1)
  have hNpos : (0 : ℝ) < (H.QS : ℝ) * H.q * H.d := by exact_mod_cast DC.cond_pos H
  have hlog := hv.log_cond_le
  have hq0X : (DC.q0H H : ℝ) < s.X' := hx1 s _ _ hs hx.1 hNpos hlog hq0le
  have hpX : (H.pde : ℝ) < s.X' := hx1 s _ _ hs hx.1 hNpos hlog hv.2.2.2.1.1
  have hpX' : (H.pde' : ℝ) < s.X' := hx1 s _ _ hs hx.1 hNpos hlog hv.2.2.2.1.2
  have hqg : ∀ i, DC.q0H H ≠ H.g i := fun i hi => by
    have hg := (hv.2.2.2.2.1 i).1
    rw [← hi] at hg
    have hXb := X'_le_b s
    have hk : (1 : ℝ) ≤ R.k := by
      have := R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ R.k)
    have hb1 : 1 ≤ s.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _)
    have h5 : s.b ≤ (R.k : ℝ) * s.b := le_mul_of_one_le_left (by linarith) hk
    have h6 : (R.k : ℝ) * s.b ≤ ((R.k : ℝ) * s.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have hK : H.ccK = ⊤ := hv.2.2.2.2.2.2.1
  have hmem : ∀ p ∈ H.levelPrimes, p = H.g 0 ∨ p = H.g 1 ∨ p = H.pde ∨ p = H.pde' ∨ p = DC.q0H H := fun p hp => by
    rw [hlev] at hp
    simpa using hp
  have hcond : ∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1 := fun p hp => by
    have h15 : ∀ z : ℕ, z % Nat.lcm 15 (H.QS * H.q * H.d) = 1 → z % (H.QS * H.q * H.d) = 1 := fun z hz => by
      rw [← Nat.mod_mod_of_dvd z (Nat.dvd_lcm_right 15 _), hz, Nat.mod_eq_of_lt hN2]
    rcases hmem p hp with h | h | h | h | h <;> rw [h]
    · exact ⟨H.g_prime 0, har.2.1 0⟩
    · exact ⟨H.g_prime 1, har.2.1 1⟩
    · exact ⟨H.pde_prime, h15 _ hpde.1⟩
    · exact ⟨H.pde'_prime, h15 _ hpde.2⟩
    · exact ⟨hp0, hmod0⟩
  obtain ⟨hcw, hc1, hc2, hc3, hc4⟩ := hx3 s R (setUnipotentTranslate H u0) (fun t => a t) (fun t => b t) hs hx.2 hR hH'.1
    (fun t => ⟨(hW t t.2).1.1, (hW t t.2).2.1⟩) (Tau R) (Equiv.refl _)
  have hM0 : 0 < M := by
    rw [hM, Nat.ceil_pos]
    have hxp : 0 < s.x := by linarith [s.one_lt_alt]
    have : 0 < GamS C s R := Real.exp_pos _
    positivity
  refine ⟨fun u => hcw (c u), ⟨0, hM0⟩, hK, hcond, hBB, fun u τ => (hc2 _ _ τ).1, fun u τ => (hc2 _ _ τ).2.1,
    fun u τ => (hc2 _ _ τ).2.2.1, fun u τ h => ((hc2 _ _ τ).2.2.2 h).1, fun u τ h => ((hc2 _ _ τ).2.2.2 h).2,
    ⟨hR, hT, hH'.1, hH'.2.1, ⟨hT2, hT3⟩, hdl, hgn, hpde, ⟨?_, hq1, hq2, hqg, ?_⟩, fun p hp => ?_, hW,
      (Fintype.card_fin M).trans hM, hc, fun u => hc1 (c u), fun u => hc3 (c u), fun u => hc4 (c u)⟩, hH'⟩
  · show DC.q0H H ∈ H.levelPrimes
    rw [hlev]; simp
  · show DC.q0H H % (leastOff (H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1)) * (H.QS * H.q * H.d)) = 1
    rw [leastOff_eq_rPrH H hK]
    exact (DC.globalTwisting_spec_fact H).2.1
  · rcases hmem p hp with h | h | h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · exact Or.inr (h ▸ hpX)
    · exact Or.inr (h ▸ hpX')
    · exact Or.inr (h ▸ hq0X)

theorem exists_chGoodW {la : ℝ} {Q : HostReq} (hH : DC.HostExQW la Q) (eps : ℝ) (he : 0 < eps) (he1 : eps < 1 / 52) :
    ∃ CT2 C8 C5 c6 Cb : ℝ, 1 ≤ C8 ∧ 0 < C5 ∧ 0 < c6 ∧ 0 < Cb ∧ ∃ S : Scales la,
      ∀ C : FC, Std C → C.CT2 = CT2 → C.P.Cpde = C8 →
      ∀ cD ≥ (0 : ℝ), ∀ ch ≥ (402 : ℝ), ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x → S.Mem s → ∀ u0 : ℕ,
        ∃ (P : PreCh) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool),
          ChGood s C C5 c6 Cb cD ch P a b c ∧ P.H.u0 = P.R.ofNat u0 ∧
            ∃ v : P.R.A, Q C5 s P.R { P.H with u0 := v } (DC.q0H P.H) := by
  obtain ⟨CT2, C8, C5, c6, Cb, xH, h8, h5, h6, hb, S, hH⟩ := hH eps he he1
  refine ⟨CT2, C8, C5, c6, Cb, h8, h5, h6, hb, S, fun C hC hT hP cD hcD ch hch => ?_⟩
  have hmid := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨xw, hw⟩ := exists_weights_in_windows eps C he he1 hC
  obtain ⟨xc, hc⟩ := exists_injective_words eps C.CGam C.P.CF he he1
    (zero_le_one.trans (hmid _ (by simp [FC.cMid]))) (zero_le_one.trans (hmid _ (by simp [FC.cMid])))
  obtain ⟨xg, hg⟩ := chGood_of_host eps C5 c6 Cb cD ch C he he1 hC hcD hch
  refine ⟨max xH (max xw (max xc xg)), fun s hs hx hS u0 => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨R, H, q0, hRV, hHT, hHG, rfl, hQ⟩ := hH s hs hx.1 hS
  obtain ⟨a, b, hab⟩ := hw s R H hs hx.2.1 hRV
  obtain ⟨c, hci, -⟩ := hc s R hs hx.2.2.1 hRV
  obtain ⟨hcW, w0, h1, h2, h3, h4, h5, h6, h7, h8, h⟩ :=
    hg s R H a b _ c u0 hs hx.2.2.2 hRV (hHT.trans hT.symm) (hP ▸ hHG) hab rfl hci
  exact ⟨@PreCh.mk R (setUnipotentTranslate H u0) h1 h2 h3 _ _ w0 hcW h4 h5 h6 h7 h8, a, b, c, h, rfl, H.u0, hQ⟩

theorem exists_chGood (hH : DC.HostExQ) (eps : ℝ) (he : 0 < eps) (he1 : eps < 1 / 52) :
    ∃ CT2 C8 C5 c6 Cb : ℝ, 1 ≤ C8 ∧ 0 < C5 ∧ 0 < c6 ∧ 0 < Cb ∧ ∃ la : ℝ, 1 < la ∧ ∃ S : Scales la,
      ∀ C : FC, Std C → C.CT2 = CT2 → C.P.Cpde = C8 →
      ∀ cD ≥ (0 : ℝ), ∀ ch ≥ (402 : ℝ), ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x → S.Mem s → ∀ u0 : ℕ,
        ∃ (P : PreCh) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool),
          ChGood s C C5 c6 Cb cD ch P a b c ∧ P.H.u0 = P.R.ofNat u0 := by
  obtain ⟨la, hla, hH⟩ := hH
  obtain ⟨CT2, C8, C5, c6, Cb, h8, h5, h6, hb, S, h⟩ :=
    exists_chGoodW (Q := fun _ _ _ _ _ => True) (HostExW.imp hH fun _ _ _ _ _ h => ⟨h, trivial⟩) eps he he1
  refine ⟨CT2, C8, C5, c6, Cb, h8, h5, h6, hb, la, hla, S, fun C hC hT hP cD hcD ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h C hC hT hP cD hcD ch hch
  refine ⟨x0, fun s hs hx hS u0 => ?_⟩
  obtain ⟨P, a, b, c, h1, h2, -⟩ := h s hs hx hS u0
  exact ⟨P, a, b, c, h1, h2⟩

theorem exists_chGood_unb (hH : DC.HostExQ) (eps : ℝ) (he : 0 < eps) (he1 : eps < 1 / 52) :
    ∃ CT2 C8 C5 c6 Cb : ℝ, 1 ≤ C8 ∧ 0 < C5 ∧ 0 < c6 ∧ 0 < Cb ∧ ∀ C : FC, Std C → C.CT2 = CT2 → C.P.Cpde = C8 →
      ∀ cD ≥ (0 : ℝ), ∀ ch ≥ (402 : ℝ), ∀ y : ℝ, ∃ s : Scale, s.eps = eps ∧ y ≤ s.x ∧ ∀ u0 : ℕ,
        ∃ (P : PreCh) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool),
          ChGood s C C5 c6 Cb cD ch P a b c ∧ P.H.u0 = P.R.ofNat u0 := by
  obtain ⟨CT2, C8, C5, c6, Cb, h8, h5, h6, hb, la, hla, S, h⟩ := exists_chGood hH eps he he1
  refine ⟨CT2, C8, C5, c6, Cb, h8, h5, h6, hb, fun C hC hT hP cD hcD ch hch y => ?_⟩
  obtain ⟨x0, h⟩ := h C hC hT hP cD hcD ch hch
  obtain ⟨s, hs, hx, hS⟩ := S.exists_mem hla.le he he1 (max x0 y)
  exact ⟨s, hs, le_of_max_le_right hx, h s hs (le_of_max_le_left hx) hS⟩

theorem ChGood.level {s : Scale} {C : FC} {C5 c6 Cb cD ch : ℝ} {P : PreCh} {a b : P.R.A → ℤ}
    {c : P.Word → Fin (P.R.k - 2) → Bool} (h : ChGood s C C5 c6 Cb cD ch P a b c) :
    P.H.levelPrimes = {P.H.g 0, P.H.g 1, P.H.pde, P.H.pde', DC.q0H P.H} ∧
      (DC.q0H P.H : ℝ) ≤ ((P.H.QS : ℝ) * P.H.q * P.H.d) ^ C.P.Cpde ∧ BoxW s P.H ∧
      QDq s.x s.eps C5 P.H.q P.H.d := by
  obtain ⟨-, -, -, -, h1, h2, -, -, -, -, -, -, ⟨-, -, h3, -⟩, h4⟩ := h.host
  exact ⟨h4, h3, h2, h1⟩

example (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) : 1 ≤ (setDiv D N h).div.HH :=
  le_max_left _ _

example {C : FC} (p : Pt C) (A : ∀ D : D7, LevelData D → DivX D → Scale → Prop) :
    p.Has (ptO fun D O => A D O.lev O.X O.L.sc) ↔ A p.D p.xa.ex.lev p.xa.X p.L.sc := Iff.rfl

example : leastOff 6 = 5 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨by norm_num, by norm_num⟩
  · refine le_csInf ⟨5, by norm_num, by norm_num⟩ ?_
    rintro r ⟨h1, h2⟩
    by_contra h
    have : r < 5 := by omega
    interval_cases r <;> simp_all (config := {decide := true})

end GlobalTheory.EX.OB

end
