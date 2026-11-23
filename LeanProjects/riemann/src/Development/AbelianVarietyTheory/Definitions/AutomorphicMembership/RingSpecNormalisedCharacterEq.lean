import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAutLoc
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwoPowS0EqTwoPartModulus
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsRowLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField
  IsDedekindDomain Polynomial
open scoped TensorProduct

structure AUSide (D : D7) where
  cls : ∀ j, 1 ≤ j → j ≤ D.R.m → NG.AutRep D.host.E D.R.nV → D.nbc.AU j
  surj : ∀ j h1 h2, Function.Surjective (cls j h1 h2)
  iso : ∀ j h1 h2 π π', cls j h1 h2 π = cls j h1 h2 π' ↔ π.Iso π'
  mult : ∀ j h1 h2 π, D.nbc.multAU j (cls j h1 h2 π) = π.mult
  sph : ∀ j h1 h2 π (w : PlE D.host) v, ¬ IsSplitPl D.host w → NG.OverPl w v →
    (D.nbc.sphAU j (cls j h1 h2 π) w ↔ π.SphAt v)
  sat : ∀ j h1 h2 π v (w : PlE D.host), NG.OverPl w v → ∀ (Dv : InertDatum D.host.E D.R.nV v w), (∃ α, NG.SatAt π Dv α) →
    ∃ α, NG.SatAt π Dv α ∧ D.nbc.satAU j (cls j h1 h2 π) w = Finset.univ.val.map α
  clsWt : ∀ j, 1 ≤ j → j ≤ D.R.m → NG.AlgWt D.host.E D.R.nV → D.nbc.Wt j
  surjWt : ∀ j h1 h2, Function.Surjective (clsWt j h1 h2)
  isoWt : ∀ j h1 h2 a b, clsWt j h1 h2 a = clsWt j h1 h2 b ↔ a.Iso b
  wt : ∀ j h1 h2 π a, π.toAlgWt.IsDual a → D.nbc.wtAU j (cls j h1 h2 π) = clsWt j h1 h2 a
  infW : ∀ j h1 h2 a (τ : D.host.E →+* ℂ) lam, a.HWAt τ lam → D.nbc.infW j (clsWt j h1 h2 a) τ = NG.infOf lam
  locUnr : ∀ j h1 h2 π (s : SplitPlace D.host.E), π.SphAt s.v → D.naut.unr (D.nbc.locAU j (cls j h1 h2 π) s.w)
  locPol : ∀ j h1 h2 π (s : SplitPlace D.host.E) (w : PlE D.host) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
    IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → ∀ J : Subgroup (GAf D.host.E D.R.nV),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV)) → ∀ f ∈ π.S, f ≠ 0 →
    (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) → ∀ c : ℕ → ℂ,
    (∀ k, 1 ≤ k → k ≤ D.R.nV → NG.tN J s ϖ k f = c k • f) →
    X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        Polynomial.C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      galPol D.naut (D.naut.lpTw (D.nbc.locAU j (cls j h1 h2 π) w) ((1 - (D.R.nV : ℝ)) / 2))

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def IsLocS {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Submodule ℂ (GAf L n → W)) (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) : Prop :=
  ∃ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : σ.V →ₗ[ℂ] (GAf L n → W)),
    Continuous i ∧ (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) ∧ Function.Injective T ∧ (∀ a, T a ∈ S) ∧
    ∀ x : GAf L n, TrivOutside {s.v} x → ∀ a,
      T (σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)

def AUTrue (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : AUSide D) : Prop :=
  ∀ j h1 h2 π (s : SplitPlace D.host.E) σ, IsLocS π.S s σ → T.e s.w (D.nbc.locAU j (A.cls j h1 h2 π) s.w) =
    GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls σ)

def RowTrue (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (par : D.what₂.FT → ∀ w : PlE D.host, GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w))
    (sat : D.what₂.FT → PlE D.host → Multiset ℂ) : Prop :=
  (∀ σ (s : SplitPlace D.host.E) τ, IsLocS (rep σ).S s τ →
    par σ s.w = GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls τ)) ∧
  ∀ σ v (w : PlE D.host), NG.OverPl w v → ∀ Dv : InertDatum D.host.E D.R.r v w, (∃ α, NG.SatAtS (rep σ).S Dv α) →
    ∃ α, NG.SatAtS (rep σ).S Dv α ∧ sat σ w = Finset.univ.val.map α

def RowDepth (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) : Prop :=
  ∀ σ k v, ∃ (s : SplitPlace D.host.E) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))),
    s.w = D.naut.plGw k v ∧ IsLocS (rep σ).S s τ ∧
      GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion D.host.E) (Fin D.R.r)) ≠ ⊥

end

def ChiTOk (D : D7) (cf : CharFrame D) : Prop :=
  ∀ k v (j : Fin D.R.m) (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0),
    NX.TameRep (D.naut.plGw k v) 1 (D.ntypes.tg k v) u → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ c : (ZMod (D.host.g k))ˣ, (c = D.nd.chiT k v j ∨ c = (D.nd.chiT k v j)⁻¹) ∧
      (((cf.mu0 j).locK (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) =
        D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (c : ZMod (D.host.g k)))

structure SideA (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) where
  bare : IsEmpty D.nd.Loc
  wdT : GlobalTheory.RowTie.WDTie D.nd D.naut
  lab : LabTrue D wdT
  chr : CharSide D cf
  row : RowSide D
  pl : PlSide D
  iota : IotaOk D pl
  wd : WDSide D wdT
  grp : GrpSide D
  par : ParSide D jE
  au : AUSide D
  chiT : ChiTOk D cf

structure MtInput (D : D7) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (Q : D.what₂.places.Pl → Finset (PlE D.host)) : Prop where
  prod : ∀ w (j : Fin D.R.m), NG.IsProdLevel (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).J
  para : ∀ w (j : Fin D.R.m), ∀ v ∈ qPl D (tup (D.what₂.muTw w) j),
    ∃ (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧
      NG.IsCompAt (tup (D.what₂.muTw w) j) s ξ ∧ NG.LevelPara (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).J (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).χ s D.R.r ξ
  uni : ∀ w (j : Fin D.R.m) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E),
    s.w = D.naut.plGw k v → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
      (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧
      NG.IsCompAt (tup (D.what₂.muTw w) j) s ξ ∧ NG.LevelUni (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).J (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).χ s D.R.r ψ₀ ξ
  hyp : ∀ w (j : Fin D.R.m), NG.HypOutside (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).J (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).χ (gPl D ∪ qPl D (tup (D.what₂.muTw w) j))
  wt : ∀ μ (j : Fin D.R.m) (t : D.what₂.Tau) (a : NG.AlgWt D.host.E D.R.nV) (lam : Fin D.R.nV → ℤ),
    (M μ (j.1 + 1) (by omega) (by omega)).wt.IsDual a → a.HWAt (embT D t) lam → NG.infOf lam = NG.paramV D.R (D.hc t) j (1 / 2)
  rat : ∀ w (j : Fin D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (Q w) v k →
    IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → ∀ x, ∃ x',
      (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).real (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x') =
        NG.tN (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).J s ϖ k ((M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).real (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))
  int : ∀ w (j : Fin D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), TwistedAt D w → GenAt D (D.what₂.places.resChar w) (Q w) v k →
    IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → ∀ y ∈ (D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen,
      ∃ c : D.what₂.Mt (D.what₂.muTw w) (j.1 + 1) → D.what₂.LL, (∀ g, 0 ≤ D.what₂.places.val w (c g)) ∧
        NG.tN (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).J s ϖ k ((M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).real y) =
          (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).real (∑ g ∈ (D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen, D.what₂.embLL (c g) • g)
  full : ∀ w (j : Fin D.R.m), TwistedAt D w →
    (∀ y ∈ (D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen, y ∈ Set.range (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1))) ∧
      Submodule.span ℂ ((D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen : Set (D.what₂.Mt (D.what₂.muTw w) (j.1 + 1))) = ⊤

def hkF (D : D7) {tw : NTw D.R D.host D.what₂ D.LL0 D.nd} (S : RatDat tw) (i : tw.Tw) (j : ℕ) (b : Bool)
    (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hs : ∀ k P (x : S.WL j), x ∈ (S.A j).WK → hL k P x ∈ (S.A j).WK)
    (k : ℕ) (P : PlE D.host) : Module.End (FractionRing (tw.O i)) (Fm S i j b) :=
  (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j)
      (((hL k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) fun x hx => hs k P x hx) :
    Module.End (KB S i b) (KB S i b ⊗[S.Ks] FmK S j))

def actL (D : D7) {tw : NTw D.R D.host D.what₂ D.LL0 D.nd} (S : RatDat tw) (j : ℕ) (g : G0g D.nd) : Module.End D.what₂.LL (S.WL j) :=
  ((((S.A j).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ • (S.A j).ρ (S.eG.symm g)

def goodL (D : D7) (S : RatDat D.ntw) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) :
    Submodule D.what₂.LL (S.WL j) :=
  Module.End.eigenspace (∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g) 1 ⊓
    ⨅ u : Formalism.IndefR.NX.U D.nd, Module.End.eigenspace (actL D S j u)
      (((psiUOf D.nd (NX.xiRed D) θ u : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL)

structure RatIn (D : D7) (S : RatDat D.ntw) where
  Sb : Finset (PlE D.host)
  rho : ∀ j, 1 ≤ j → j ≤ D.R.m → RhoStab S j
  chi : ∀ j, 1 ≤ j → j ≤ D.R.m → ChiInLL0 S j
  ks : ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm
  fd : ∀ j, 1 ≤ j → j ≤ D.R.m → FiniteDimensional S.Ks (FmK S j)
  mk_fg : ∀ j, 1 ≤ j → j ≤ D.R.m → ∃ T : Finset (S.WL j), (∀ x ∈ T, x ∈ (S.A j).MK) ∧
    (∀ x ∈ (S.A j).MK, x ∈ (S.A j).WK ∧ x ∈ Submodule.span (𝓞 S.Ks) (T : Set (S.WL j))) ∧
    ∀ x ∈ (S.A j).WK, x ∈ Submodule.span S.Ks (T : Set (S.WL j))
  hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)
  hs : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ k P (x : S.WL j), x ∈ (S.A j).WK → hL j k P x ∈ (S.A j).WK
  hL_zero : ∀ j P, hL j 0 P = 1
  θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ
  θ_ne : ∀ kk, θ kk ≠ 1
  eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0
  span : ∀ j, 1 ≤ j → j ≤ D.R.m → goodL D S θ j ≤
    ⨆ σ ∈ {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}, goodL D S θ j ⊓ ⨅ (k : ℕ) (P : PlE D.host)
      (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ Sb), Module.End.eigenspace (hL j k P) ((eig j σ k P : ↥D.LL0) : D.what₂.LL)
  hL_int : ∀ j k P, 1 ≤ j → j ≤ D.R.m → IsSplitPl D.host P → P ∉ Sb → k ≤ D.R.r → ∃ n : ℕ,
    ∀ x ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), x ∈ goodL D S θ j →
      (normV P) ^ n • hL j k P x ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j))

structure TwNew (D : D7) where
  tw : NTw D.R D.host D.what₂ D.LL0 D.nd
  ex : NExp D.R D.host D.what₂ D.LL0 D.nd tw
  h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g
  th : NTh D.R D.host D.what₂ D.LL0 D.nd tw ex
  br : ∀ (i : tw.Tw) (w : PlE D.host), w ∈ placesOver D.host.E (tw.l i) →
    LocBridge (tw.l i) D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) (tw.O0 i)
  hbr : ∀ (i : tw.Tw) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (tw.l i)) (x : D.nd.Om),
    x ∈ D.nd.plOm.1 w ↔ ‖(br i w hw).j x‖ ≤ 1

def TwNew.toD7 {D : D7} (N : TwNew D) : D7 := setTw D N.tw N.ex N.h0 N.th N.br N.hbr

def TwNew.cf {D : D7} (N : TwNew D) (c : CharFrame D) : CharFrame N.toD7 :=
  ⟨c.P, c.W, c.mu0, c.eta, c.chiPsi, c.del, c.del', c.isMu0, c.isEta, c.isChi, c.isDel, c.isDel'⟩

def TwNew.row {D : D7} (N : TwNew D) (r : RowSide D) : RowSide N.toD7 := ⟨r.locR, r.satR, r.lab_eq⟩

def TwNew.rat {D : D7} (N : TwNew D) (S : RatDat D.ntw) : RatDat N.toD7.ntw := { S with }

def TwNew.mt {D : D7} (N : TwNew D) (M : MtFam D) : MtFam N.toD7 := fun μ j h1 h2 => { M μ j h1 h2 with }

set_option synthInstance.maxHeartbeats 400000 in

structure SideB (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) where
  twF : TwFrameC D
  tw : TwistFrameLowIndexCompatibility D twF low
  cover : ∀ w : D.what₂.places.Pl, ∃ i, D.ntw.l i = D.what₂.places.resChar w ∧ SidePl D w i true
  chiD : NC.NChiData D
  chi : NC.NormalizedCharacterCompatibility D chiD
  eta_eq : ∀ x, chiD.etaT.χ x = cf.eta.1 x
  ringSpec_normalisedCharacter_eq : ∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x
  del_eq : ∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x
  iCq_embO : ∀ s (x : ↥D.LL0), twF.iCq s (chiD.embO s true x) = D.what₂.embLL (x : D.what₂.LL)
  embO_star : ∀ s (x y : ↥D.LL0), (y : D.what₂.LL) = star (x : D.what₂.LL) → chiD.embO s false x = chiD.embO s true y
  deltaRead : DeltaRead D cf
  exp : NExpTied D
  pq : ∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hadm : NX.AdmTw D i k Q ψ),
    (exp.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf D Pq Q ∧ (exp.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf D Pq (D.ntw.pD i)
  psiU : ∀ i b (u : G0g D.nd) (hu : u ∈ D.nexp.U) (hu' : u ∈ Formalism.IndefR.NX.U D.nd),
    ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      readLL0 S i b ((psiUOf D.nd (NX.xiRed D) θ ⟨u, hu'⟩ : (↥D.LL0)ˣ) : ↥D.LL0)
  rho : ∀ j, 1 ≤ j → j ≤ D.R.m → RhoStab S j
  chiL : ∀ j, 1 ≤ j → j ≤ D.R.m → ChiInLL0 S j
  hs : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ k P (x : S.WL j), x ∈ (S.A j).WK → hL j k P x ∈ (S.A j).WK
  eF : ∀ i j b, 1 ≤ j → j ≤ D.R.m → D.nexp.Fm i j b ≃ₗ[FractionRing (D.ntw.O i)] Fm S i j b
  bsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b), x ∈ D.nexp.Bsup i j b ↔ eF i j b h1 h2 x ∈ Bsup S i j b
  act : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (g : G0g D.nd) (x : D.nexp.Fm i j b),
    eF i j b h1 h2 (D.nexp.actG i j b g x) = actG S i j b (rho j h1 h2) (chiL j h1 h2) g (eF i j b h1 h2 x)
  cHk : ∀ i (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ
  hkEq : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (x : D.nexp.Fm i j b), P ∉ D.ntw.S0 i →
    IsSplitPl D.host P → k ≤ D.R.r → eF i j b h1 h2 (D.nexp.hkF i j b k P x) =
      algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (cHk i b P) ^ k • hkF D S i j b (hL j) (hs j h1 h2) k P (eF i j b h1 h2 x)
  cHk_del : ∀ i b P, P ∉ D.ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
    cHk i b P = Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom (if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹)
  hk_emb : ∀ i j b k P (x : D.ntw.B i j b), 1 ≤ j → j ≤ D.R.m → P ∉ D.ntw.S0 i → IsSplitPl D.host P → k ≤ D.R.r →
    D.nexp.embB i j b (D.ntw.hk i j b k P x) = D.nexp.hkF i j b k P (D.nexp.embB i j b x)
  sigSpan : D.ntw.SigSpan
  rowS : ∀ i, D.ntw.Sig i → D.what₂.FT
  rowS_eig : ∀ i (s : D.ntw.Sig i) k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i →
    algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.hEig i s k P) =
      algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (cHk i (D.ntw.side i s) P) ^ k *
        (show FractionRing (D.ntw.O i) from readLL0 S i (D.ntw.side i s) (eig (D.ntw.jS i s) (rowS i s) k P))
  hEig_zero : ∀ i (s : D.ntw.Sig i) P, D.ntw.hEig i s 0 P = 1
  rhoS : RhoSpec D Rw rowS

set_option synthInstance.maxHeartbeats 400000 in

structure ChoiceSide (D : D7) (cf : CharFrame D) (mt : MtFam D) (exp : NExpTied D) (C : NChoice D) (tp : TupTied D cf C) : Prop where
  nct : NChTie D C
  choice : ChoiceC D C
  off : ∀ w, ¬ TwistedAt D w → C.Q w = ∅
  adm : ∀ w, TwistedAt D w → NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w)))
  psi : PsiChoiceCompatible D cf C tp
  eMt_level : ∀ (w : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : TwistedAt D w) (hA : NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w)))),
    ∃ ι : FractionRing (C.Oe w) →+* ℂ, (∀ x : D.what₂.LL, ι (C.embW w x) = D.what₂.embLL x) ∧
      (mt (D.what₂.muTw w) j h1 h2).J =
        (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J ∧
      ∀ (κ : Formalism.AUTREP.GAf D.host.E D.R.nV) (h : κ ∈ (mt (D.what₂.muTw w) j h1 h2).J)
        (h' : κ ∈ (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
          ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J),
        (((mt (D.what₂.muTw w) j h1 h2).χ ⟨κ, h⟩ : ℂˣ) : ℂ) =
          ι (C.kMapE w (((exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
            ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).χ ⟨κ, h'⟩ : (NX.Kk D (C.twI w) (C.k' w))ˣ) :
              NX.Kk D (C.twI w) (C.k' w)))

section Loc
variable {D : D7}

def mlX (M : MtFam D) (X : LocNd (lay0 D)) (i : X.nd.Loc) : MtReal D (X.nd.mu i) (X.nd.j i) :=
  M (X.nd.mu i) (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2

def castX (X : LocNd (lay0 D)) {j : ℕ} {w : D.what₂.places.Pl} {i : X.nd.Loc} (h : i ∈ X.nd.locs j w)
    (x : D.what₂.MtL (X.nd.mu i) (X.nd.j i)) : D.what₂.MtL (D.what₂.muTw w) j :=
  cast (by obtain ⟨h1, h2⟩ := (X.nd.locs_mem j w i).1 h; subst h1; subst h2; rw [X.nd.mu_w]) x

set_option synthInstance.maxHeartbeats 400000 in

structure NdSpec (Pl : PlSide D) (M : MtFam D) (C : NChoice D) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D))
    (T : LocTw X) where
  iq : ∀ i : X.nd.Loc, FractionRing (X.nd.O i) →+* Qbar (X.nd.l i)
  iq_alg : ∀ i (z : ℤ_[X.nd.l i]), iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
    (algebraMap ℤ_[X.nd.l i] (X.nd.O i) z)) = algebraMap ℚ_[X.nd.l i] (Qbar (X.nd.l i)) (z : ℚ_[X.nd.l i])
  iq_LL : ∀ i x, qCast (X.nd.w_l i) (Pl.ι (X.nd.w i)) (iq i (X.nd.embK i x)) = D.what₂.embLL x
  iq_big : ∀ i, ∀ z ∈ big (X.nd.w i), ∃ x, qCast (X.nd.w_l i) (Pl.ι (X.nd.w i)) (iq i x) = z
  B : NLocBase D M
  Q_eq : ∀ j w i, i ∈ X.nd.locs j w → X.nd.Q i = B.Qc j w
  mx : ∀ j w, X.nd.Loc → Ideal (heckeAlg B j w)
  mx_max : ∀ j w i, i ∈ X.nd.locs j w → (mx j w i).IsMaximal
  mx_inj : ∀ j w, Set.InjOn (mx j w) (X.nd.locs j w)
  mx_all : ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → ∀ I : Ideal (heckeAlg B j w), I.IsMaximal →
    ∃ i ∈ X.nd.locs j w, mx j w i = I
  phO : ∀ j w i, i ∈ X.nd.locs j w → X.nd.O i ≃+* B.Oc j w
  phK : ∀ j w i, i ∈ X.nd.locs j w → FractionRing (X.nd.O i) ≃+* FractionRing (B.Oc j w)
  phK_alg : ∀ j w i (h : i ∈ X.nd.locs j w) (z : X.nd.O i),
    phK j w i h (algebraMap _ _ z) = algebraMap _ _ (phO j w i h z)
  phK_emb : ∀ j w i (h : i ∈ X.nd.locs j w) (x : D.what₂.LL), phK j w i h (X.nd.embK i x) = B.ec j w x
  Psi : ∀ j w i (h : i ∈ X.nd.locs j w),
    TensorProduct (X.nd.O i) (FractionRing (X.nd.O i)) (X.nd.Mt i) →ₛₗ[(phK j w i h).toRingHom] B.V j w
  Psi_inj : ∀ j w i (h : i ∈ X.nd.locs j w), Function.Injective (Psi j w i h)
  Psi_range : ∀ j w i (h : i ∈ X.nd.locs j w) (y : B.V j w),
    y ∈ NCov.part (heckeAlg B j w) (mx j w i) ↔ ∃ z, Psi j w i h z = y
  Psi_pr : ∀ j w i (h : i ∈ X.nd.locs j w) (x : D.what₂.MtL (X.nd.mu i) (X.nd.j i)),
    Psi j w i h (X.nd.prMt i x) - B.iV j w (castX X h x) ∈ NCov.off (heckeAlg B j w) (mx j w i)
  ptX : ∀ j w i (h : i ∈ X.nd.locs j w), X.nd.X i ≃
    {ψ : heckeAlg B j w →ₐ[B.Oc j w] B.Oc j w //
      NCov.cls ψ = mx j w i ∧ NCov.W (heckeAlg B j w) (NCov.pt ψ) ≠ ⊥}
  ptX_hT : ∀ j w i (h : i ∈ X.nd.locs j w) (x : X.nd.X i) (v : PlE D.host) (k : ℕ)
    (hvk : GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k),
    phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x) =
      (ptX j w i h x).1 ⟨B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩
  iotaC : ∀ j w, B.Oc j w →+* ℂ
  iotaC_coh : ∀ j w i (h : i ∈ X.nd.locs j w) (z : X.nd.O i),
    qCast (X.nd.w_l i) (Pl.ι (X.nd.w i)) (iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) z)) = iotaC j w (phO j w i h z)
  Qc_eq : ∀ j w, B.Qc j w = C.Q w
  std : HeckeStd B
  act_hK : ∀ j w i (h : i ∈ X.nd.locs j w) v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∀ z,
    Psi j w i h (((X.nd.act i (X.nd.hT i v k)).baseChange (FractionRing (X.nd.O i))) z) = B.hK j w v k (Psi j w i h z)
  twOf_eq : ∀ a, T.twOf a = C.twI (X.nd.w a)
  twSide_eq : ∀ a, T.twSide a = C.sd (X.nd.w a)
  psi_eq : ∀ (a : X.nd.Loc) (g : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (y : D.what₂.LL), C.embW (X.nd.w a) y =
      algebraMap (C.Oe (X.nd.w a)) (FractionRing (C.Oe (X.nd.w a)))
        (algebraMap (D.ntw.Ok (C.twI (X.nd.w a)) (C.k' (X.nd.w a))) (C.Oe (X.nd.w a))
          ((C.psi' (X.nd.w a) (D.ntw.art (C.twI (X.nd.w a)) (C.Q (X.nd.w a)) g) :
            (D.ntw.Ok (C.twI (X.nd.w a)) (C.k' (X.nd.w a)))ˣ) : D.ntw.Ok (C.twI (X.nd.w a)) (C.k' (X.nd.w a)))) →
    X.nd.embK a y = algebraMap (X.nd.O a) (FractionRing (X.nd.O a)) ((T.psiL a g : (X.nd.O a)ˣ) : X.nd.O a)
  twO_alg : ∀ a, haveI : Fact (D.ntw.l (T.twOf a)).Prime := D.ntw.lPrime (T.twOf a); ∀ (z : ℤ_[D.ntw.l (T.twOf a)]) (z' : ℤ_[X.nd.l a]), HEq z z' →
    T.twist₂ a (@algebraMap _ (D.ntw.O0 (T.twOf a)) _ _ (D.ntw.algO0 (T.twOf a)) z) = algebraMap _ (X.nd.O a) z'
  tw_reads : ∀ a : X.nd.Loc, ∃ f : D.ntw.O0 (C.twI (X.nd.w a)) →+* X.nd.O a, HEq f (T.twist₂ a) ∧
    ∃ (Ω : Type) (_ : Field Ω) (τ : FractionRing (X.nd.O a) →+* Ω) (ι : FractionRing (C.Oe (X.nd.w a)) →+* Ω),
      (∀ y, τ (algebraMap (X.nd.O a) (FractionRing (X.nd.O a)) (f y)) =
        ι (algebraMap (C.Oe (X.nd.w a)) (FractionRing (C.Oe (X.nd.w a)))
          (algebraMap (D.ntw.Ok (C.twI (X.nd.w a)) (C.k' (X.nd.w a))) (C.Oe (X.nd.w a))
            (BlochKatoReduction.Gen.phiK D.ntw (C.twI (X.nd.w a)) (C.k' (X.nd.w a)) y)))) ∧
      ∀ x : D.what₂.LL, τ (X.nd.embK a x) = ι (C.embW (X.nd.w a) x)
  heckeLoc_gamma_places : ∀ i k v, X.nd.gam0 i (D.naut.plGw k v) = D.ntypes.tg k v
  nbr : ∀ (i : X.nd.Loc) (w : PlE D.host), w ∈ placesOver D.host.E (X.nd.l i) →
    LocBridge (X.nd.l i) D.host.E X.nd.Om (Dec (F := D.host.E) (X.nd.plOm.1 w)) (X.nd.O i)
  nbr_ind : ∀ i w (hw : w ∈ placesOver D.host.E (X.nd.l i)) (x : X.nd.Om), x ∈ X.nd.plOm.1 w ↔ ‖(nbr i w hw).j x‖ ≤ 1
  self_good : ∀ i w (hw : w ∈ placesOver D.host.E (X.nd.l i)), Formalism.BasicNotions.Loc.GoodCoef D.host.condN (nbr i w hw).LL
  nbr_iq : ∀ i w (hw : w ∈ placesOver D.host.E (X.nd.l i)) (x : X.nd.O i),
    iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) x) = (((nbr i w hw).toLL x : ↥(nbr i w hw).LL.1) : Loc.Om (X.nd.l i))
  bj : ∀ i, (D.what₂.MjLat (X.nd.j i)).gen → X.nd.Bj i
  bj_span : ∀ i, Submodule.span (X.nd.O i) (Set.range (bj i)) = ⊤
  bj_rel : ∀ i (s : D.what₂.O →+* X.nd.O i),
    (∀ y, algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) (s y) = X.nd.embK i (D.what₂.OtoLL y)) →
    ∀ c : (D.what₂.MjLat (X.nd.j i)).gen → X.nd.O i, ∑ g, c g • bj i g = 0 ↔
      c ∈ Submodule.span (X.nd.O i) ((fun r => s ∘ r) '' latRel (D.what₂.MjLat (X.nd.j i)))

set_option synthInstance.maxHeartbeats 400000 in

structure AutSpec {cf : CharFrame D} {jE : D.host.E →+* Qb} (A : SideA D cf jE) (M : MtFam D)
    (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) {X : LocNd (lay0 D)}
    (iq : ∀ i : X.nd.Loc, FractionRing (X.nd.O i) →+* Qbar (X.nd.l i)) (Y : LocAut X) (Cb : LocBC Y) where
  iotaQ : ∀ i, Y.naut.iotaQ i = iq i
  iotaQC : ∀ i : X.nd.Loc, Y.naut.iotaQC i = qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))
  kFbar : ∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ A.pl.plB (X.nd.w i),
    fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out
      (A.pl.plκ (X.nd.w i) (IsLocalRing.residue (A.pl.plB (X.nd.w i)) ⟨_, h⟩)) =
      Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)
  locW : ∀ i σ w, Y.locW i σ w = A.row.locR σ w
  satW : ∀ i σ w, Y.satW i σ w = A.row.satR σ w
  wdOf : ∀ (i : X.nd.Loc) a (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (X.nd.l i))) w,
    Y.wdOf i r w = A.wd.wdOf (X.nd.l i) (Y.naut.iotaQC i) r w ∧
    (Y.IsCrysW i r w ↔ A.wd.IsCrysW (X.nd.l i) (Y.naut.iotaQC i) r w) ∧
    (Y.IsPotCrysW i r w ↔ A.wd.IsPotCrysW (X.nd.l i) (Y.naut.iotaQC i) r w) ∧
    (Y.IsdRW i r w ↔ A.wd.IsdRW (X.nd.l i) (Y.naut.iotaQC i) r w) ∧
    ∀ τ, Y.jumpsW i r τ = A.wd.jumpsW (X.nd.l i) (Y.naut.iotaQC i) r τ
  muC : ∀ i (j : Fin D.R.m), j.1 + 1 = X.nd.j i → (A.chr.e1 (Y.muC i)).1 = tup (X.nd.mu i) j
  S : ∀ i, Y.naut.AV i → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)
  irr : ∀ i P, NG.IsIrrRep (mlX M X i).wt.ρ (S i P)
  inj : ∀ i P P', NG.IsoRep (S i P) (S i P') → P = P'
  surj : ∀ i S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ →
    ∃ P, NG.IsoRep (S i P) S'
  typeV : ∀ i P, Y.naut.typeV i P = (NG.isoTyp (mlX M X i).wt.ρ (S i P)).comap (mlX M X i).real
  ptV : ∀ i P x, Y.naut.ptV i P = some x ↔ ∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w →
    IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ Y.naut.typeV i P,
    NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = iotaO X.nd Y.naut i ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y
  emb : ∀ i P, Cb.embAV i P = A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
    { (mlX M X i).wt with S := S i P, irrS := irr i P }

def withLoc (L : LocAll (lay0 D)) : D7 := setN D L.lay

set_option maxHeartbeats 1000000 in

def mtL (L : LocAll (lay0 D)) (M : MtFam D) : MtFam (withLoc L) := fun μ j h1 h2 => { M μ j h1 h2 with }

set_option maxHeartbeats 2000000 in

def chL (L : LocAll (lay0 D)) (C : NChoice D) : NChoice (withLoc L) := { C with }

def cfL (L : LocAll (lay0 D)) (c : CharFrame D) : CharFrame (withLoc L) := cfTr L.lay c

set_option maxHeartbeats 1000000 in

def tpL (L : LocAll (lay0 D)) {c : CharFrame D} {C : NChoice D} (tp : TupTied D c C) : TupTied (withLoc L) (cfL L c) (chL L C) :=
  { tp with }

end Loc

structure HeckeOpen (D : D7) (mt : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) where
  hecke : HeckeTied D mt
  av : AVTied D mt
  au : AUSide D
  emb : ∀ i P, D.nbc.embAV i P = au.cls (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (av.rep i P)
  rational : HeckeRational D mt
  level : LevelTied D mt tup
  data : NormalizedDataCompatibility D
  cover : NormalizedLocalCompatibility D mt

set_option synthInstance.maxHeartbeats 400000 in

structure TypesOpen (D : D7) (jE : D.host.E →+* Qb) where
  grp : GrpSide D
  par : ParSide D jE
  plB : D.what₂.places.Pl → ValuationSubring ℂ
  plκ : ∀ w, haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    IsLocalRing.ResidueField (plB w) ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar w)
  plB_loc : ∀ (i : D.nd.Loc) (y : D.nd.O i),
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    ∃ h : iotaOC D i y ∈ plB (D.nd.w i),
      fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (plκ (D.nd.w i) (IsLocalRing.residue (plB (D.nd.w i)) ⟨_, h⟩)) =
        D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)
  plB_iota : ∀ (i : D.nd.Loc) k v x,
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    D.ntypes.iota k v (D.nd.w i) x = redThrough (plB (D.nd.w i)) (plκ (D.nd.w i)) (D.ntypes.teichC k x)
  rbarSS : ∀ (σ : D.what₂.FT) (lam : D.what₂.places.Pl), (∃ a : D.nd.Loc, D.nd.w a = lam) →
    Formalism.MainNotions.N.IsSSRep (D.ntypes.rbar σ lam)
  rbar : ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
    ∀ (Sig : List (Part D.naut.CG)) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)),
      Formalism.MainNotions.N.HasParamW D.nd D.naut i σ Sig → Formalism.MainNotions.N.IsRepOfSig D.nd D.naut i Sig ρ →
      ∀ g, (((D.ntypes.rbar σ (D.nd.w i) g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).map
          (Formalism.MainNotions.N.fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom =
        ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
          ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i)))

set_option synthInstance.maxHeartbeats 400000 in

structure TwOpen (D : D7) (C : NChoice D) (cf : CharFrame D) (tp : TupTied D cf C) (mt : MtFam D) (low : Finset ℕ) where
  chiD : NC.NChiData D
  chi : NC.NormalizedCharacterCompatibility D chiD
  twF : TwFrameC D
  tw : TwistFrameLowIndexCompatibility D twF low
  exp : NExpTied D
  ch : ChoiceSide D cf mt exp C tp
  eta_eq : ∀ x, chiD.etaT.χ x = cf.eta.1 x
  ringSpec_normalisedCharacter_eq : ∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x
  del_eq : ∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x
  psi_eq : ∀ a x, (chiD.psi a).χ x = (tp.psi (D.nd.w a)).1 x
  etaT_link : ∀ (w : PlE D.host) (α : ℂ), chiD.etaT.At w α →
    D.naut.frobEig (D.naut.locG D.naut.etaT w) = {α⁻¹}
  muC_link : ∀ i : D.nd.Loc, ∀ᶠ w in Filter.cofinite, ∀ α : ℂ,
    (chiD.mu0 (D.nd.j i) * chiD.del (D.ntw.twOf i) * chiD.psi i).At w α →
    D.naut.frobEig (D.naut.locG (D.naut.muC i) w) = {α⁻¹}
  iCq_embO : ∀ s (x : ↥D.LL0), twF.iCq s (chiD.embO s true x) = D.what₂.embLL (x : D.what₂.LL)
  embO_star : ∀ s (x y : ↥D.LL0), (y : D.what₂.LL) = star (x : D.what₂.LL) → chiD.embO s false x = chiD.embO s true y
  chrN : NCharTied D cf C tp
  chrGal : NGalChrTied D cf C tp

structure NBuilt (hLL : GlobalTheory.Published.LocalLanglandsGL) (D' : D7) where
  D : D7
  cf : CharFrame D
  jE : D.host.E →+* Qb
  A : SideA D cf jE
  cg : CGTrue hLL D A.wdT
  au : AUTrue hLL D A.wdT A.au
  rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r
  row : RowTrue hLL D rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR
  low : Finset ℕ
  Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host
  S : RatDat D.ntw
  hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)
  eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0
  θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ
  Bs : SideB D cf A.row low Pq S hL eig θ
  M : MtFam D
  C : NChoice D
  tp : TupTied D cf C
  ch : ChoiceSide D cf M Bs.exp C tp
  mt : MtInput D M tp.tup C.Q
  big : D.what₂.places.Pl → Finset ℂ
  L : LocAll (lay0 D)
  Sp : NdSpec A.pl M C big L.X L.T
  Au : AutSpec A M tp.tup Sp.iq L.Y L.C
  ss : ∀ σ lam, IsSSRep (L.Z.rbar σ lam)
  eq : D' = withLoc L

structure NTrue (hLL : GlobalTheory.Published.LocalLanglandsGL) (D' : D7) (cf' : CharFrame D') (C' : NChoice D') (tp' : TupTied D' cf' C')
    extends NBuilt hLL D' where
  pack : (⟨D', cf', C', tp'⟩ : Σ (D₁ : D7) (c₁ : CharFrame D₁) (C₁ : NChoice D₁), TupTied D₁ c₁ C₁) =
    ⟨withLoc L, cfL L cf, chL L C, tpL L tp⟩

end GlobalTheory.HeightCounting

end
