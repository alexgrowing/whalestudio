import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {D : D7}

def UnitRatio (S : ℕ → Prop) (x y : ℂ) : Prop :=
  y ≠ 0 ∧ ∃ n : ℕ, 0 < n ∧ ∃ r : ℚ, r ≠ 0 ∧ (x / y) ^ n = (r : ℂ) ∧ ∀ p : ℕ, p.Prime → padicValRat p r ≠ 0 → S p

structure Base (c : Comm D) where
  Λ : ∀ j, GlobalTheory.FinPl.Lat (c.V j)
  β : ∀ j, GL (Fin (c.V j).rank) (Lev.EAf D)
  b : ∀ j, GA D (c.V j)

  ΛT : GlobalTheory.FinPl.Lat c.T
  βT : GL (Fin c.T.rank) (Lev.EAf D)
  bT : GA D c.T
  LT : GlobalTheory.FinPl.Lat c.T
  Pg : Finset (Formalism.L2.DIV.Pl D.host.E)
  P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ

variable {c : Comm D}

open Classical in

def Base.S (B : Base c) : Finset (GlobalTheory.FinPl.Pl D) := B.Pg.image fun PP => PP.under (𝓞 D.host.F)

def Base.offS (B : Base c) (v : GlobalTheory.FinPl.Pl D) : Prop := v ∉ B.S

def Base.onS (B : Base c) (v : GlobalTheory.FinPl.Pl D) : Prop := v ∈ B.S

section Off

open GlobalTheory.FinPl

structure Off (B : Base c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : Type) where
  p : ι → SplitPt D k

  I : List ι

  q : Unif k

  χ : ι → AddChar k Circle
  hχ : ∀ i, HasConductor (χ i) 1

  β : ∀ j i, Frame (p i) (c.X j) (Fin (c.X j).rank)

  Q : ∀ j, ι → Pair k (Fin (c.X j).rank)

  β₀ : ∀ j ρ h i, Frame (p i) (c.bes j ρ h).V₀ (Fin (c.X j).rank ⊕ Fin 1)

  L : ∀ j, Lat (c.V j)

  M : ∀ j ρ h, Lat (c.bes j ρ h).V₀

  cT : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ

  cG : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ

  τ : ∀ j (h : j + 2 * 0 + 2 = D.R.m), Matrix (Fin (c.bes j 0 h).L.rank) (Fin c.Lz.rank) D.host.E

  ζ₀ : Fin c.Lz.rank → D.host.E

  γ : ∀ i, Frame (p i) c.T (Fin c.T.rank)

  γ₀ : ∀ n, n = D.R.m → ∀ i, Frame (p i) (c.X n) (Fin c.T.rank ⊕ Fin 1)

variable {B : Base c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  (o : Off B k ι)

namespace Off

def atT (v : Pl D) : Prop := ∃ i, v = (o.p i).v

def pair (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) : PairDat o.p (c.X j) (c.bes j ρ h).V₀ (Fin (c.X j).rank) :=
  ⟨o.β j, o.β₀ j ρ h, o.Q j⟩

def mid (j : ℕ) : MidDat o.p (c.X j) (Fin (c.X j).rank) := ⟨o.β j, o.Q j⟩

def Ram (j : ℕ) (φ : GA D (c.X j) → ℂ) : Prop := IsContAut (c.X j) φ ∧ ∀ i, RamAt (o.β j i) (o.Q j i) φ

def dbl (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) :
    DblLat (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) :=
  ⟨o.L j, o.M j (σ + 1) h, o.L (j + 1), (c.x (j + 1)).L, o.L (j + 1 + 1), o.M (j + 1 + 1) σ (idx_step h)⟩

end Off

structure PinOff : Prop where
  nodup : o.I.Nodup
  all : ∀ i, i ∈ o.I
  inj : Function.Injective fun i => (o.p i).v
  off : ∀ i, B.offS (o.p i).v
  char : ∀ i, (o.p i).IsChar c.ψ (o.χ i) ∧ (o.p i).UnitAA
  moves : ∀ j, j < D.R.m → IsSelfDualC (c.V j) (o.L j) ∧ ∀ P, Moves (c.V j) (B.b j) (B.Λ j) (o.L j) P
  latT : ∀ j, j ≤ D.R.m → ∀ i, (o.β j i).IsLat (c.x j).L (o.Q j i).lat
  core : ∀ j ρ h v, B.offS v → ¬ o.atT v → ∃ LL, IsSelfDualC (c.bes j ρ h).L LL ∧ OrthAt (c.bes j ρ h).o (o.M j ρ h) (c.x j).L LL v
  rep : ∀ j, j < D.R.m → ∀ f, Vac c.ψ _ _ (c.x j).L (c.x (j + 1)).L o.atT f →
    OverAll c.ψ (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) o.I f
      (comb c.ψ _ _ (o.cT j) f)
  line : IsLineVec c.Lz o.ζ₀

  tau : ∀ j h, (o.τ j h)ᴴ ⬝ ((c.bes j 0 h).L.gram ⬝ o.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram ∧
    ∃ lam : D.host.E, o.τ j h *ᵥ o.ζ₀ = lam • (c.bes j 0 h).ζ ∧ ∀ i, valuation k ((o.p i).pr (incA D lam)) = 1

  top : ∀ j (h : j + 2 * 0 + 2 = D.R.m) v, B.offS v → ¬ o.atT v → ∃ (LL : Lat (c.bes j 0 h).L) (LZ : Lat c.Lz),
    IsSelfDualC _ LL ∧ IsSelfDualC _ LZ ∧ OrthAt (c.bes j 0 h).o (o.M j 0 h) (c.x j).L LL v ∧
    OrthAt (c.oT (j + 1 + 1) h) (c.x (j + 1 + 1)).L B.LT LZ v ∧
    ∀ w ∈ latO (c.X (j + 1)) c.Lz ((c.x (j + 1)).L : Set _) (LZ : Set _) (· = v),
      kap (o.τ j h) (c.X (j + 1)) w ∈ latO (c.bes j 0 h).L (c.X (j + 1)) (LL : Set _) ((c.x (j + 1)).L : Set _) (· = v)
  topT : ∀ n (h : n = D.R.m) i, IsSumFrame (c.oT n h) o.ζ₀ (o.γ i) (o.γ₀ n h i) ∧
    ∃ (Λ : Submodule 𝒪[k] (Fin c.T.rank → k)) (s : 𝓀[k]ˣ), (o.γ i).IsLat B.LT Λ ∧
      (∀ y, y ∈ (o.Q n i).ker ↔ ((o.γ₀ n h i).b' * (o.β n i).b) *ᵥ y ∈ lastKer Λ) ∧
      (o.Q n i).HasVal (((o.β n i).b' * (o.γ₀ n h i).b) *ᵥ (o.q.inv • avec k (Fin c.T.rank) 1 1)) s
  fin : (∀ j, B.b j ∈ GfC (c.V j)) ∧ B.bT ∈ GfC c.T
  movesT : IsSelfDualC c.T B.LT ∧ ∀ P, Moves c.T B.bT B.ΛT B.LT P
  good : ∀ j ρ h v, B.offS v → GoodBF c.ψ (c.B j ρ h) (c.J j ρ h) (o.L j) (o.M j ρ h) (o.L (j + 1)) (c.x (j + 1)).L v
  adapt : ∀ j σ h v, B.offS v → AdaptFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (o.L (j + 1)) (c.x (j + 1)).L
    (o.L (j + 1 + 1)) (o.M (j + 1 + 1) σ (idx_step h)) v
  glued : ∀ j ρ h i, GluedCore (c.B j ρ h) (o.M j ρ h) o.q (o.β j i) (o.β₀ j ρ h i) (o.Q j i)
  supp : ∀ j, j < D.R.m → CombAt o.atT (o.cT j) ∧ CombAt B.onS (o.cG j)

end Off

section AtLevel

open GlobalTheory.LocMod

structure GAt (B : Base c) (τ : ∀ j h, Matrix (Fin (c.bes j 0 h).L.rank) (Fin c.Lz.rank) D.host.E)
    (PP : Formalism.L2.DIV.Pl D.host.E) where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  [mea : MeasurableSpace k]
  [bor : BorelSpace k]
  ν : Measure k
  unitVol : IsUnitVol ν
  q : GlobalTheory.FinPl.SplitPt D k
  idem : Formalism.L2.NTheta.IsIdemAt q.e PP
  unit : q.UnitAA
  s : ℕ
  hs : s + 1 + 1 = D.R.m
  S : SymData k s D.R.k
  char : (ofSplit q).IsChar c.ψ S.ψ
  FX : ∀ j, j ≤ s + 1 → Frame k (c.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)
  FT : Frame k c.T.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))
  FM : Frame k (c.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)
  FY : ∀ j cc, j + cc = s + 1 → Frame k (c.V j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin cc)
  sc : ℕ → k
  sc_unit : ∀ j, valuation k (sc j) = 1
  sc_step : ∀ j, sc (j + 1 + 1) = sc j * (ofSplit q).xi
  hz_unit : ∀ j ρ h, valuation k ((ofSplit q).hz (c.B j ρ h)) = 1
  bes : ∀ j ρ h cc (hc : j + cc = s + 1), (ofSplit q).IsBesFrame (c.B j ρ h) (sc j) (FX j (by omega)) (FY j cc hc)
  jac : ∀ j ρ h cc (hc : j + 1 + cc = s + 1), (ofSplit q).IsJacFrame (c.J j ρ h) (sc j)
    ((ofSplit q).hz (c.B j ρ h)) (FX (j + 1) (by omega)) (FY (j + 1) cc hc)
  z₀ : Fin c.Lz.rank → k
  last : FM.β = fromCols ((c.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
    (Matrix.of fun r _ => ((c.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r)
  tau : ∀ h, (τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * sc s)) • fun i => (ofSplit q).pr ((c.bes s 0 h).ζ i)
  latX : ∀ j hj (y : XIx (Fin D.R.k) (Fin D.R.t) j → k), (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec (((FX j hj).β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (c.X j) (c.x j).L (· = q.v)
  latM : ∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k, (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec ((FM.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (c.X (s + 1 + 1)) (c.x (s + 1 + 1)).L (· = q.v)
  frame : ∀ j cc (hc : j + cc = s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) j ≃ Fin (c.V j).rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) (c.V j) (B.b j) (B.β j)
      (((FY j cc hc).β * ((S.T (Fin D.R.t)).bas j cc hc).val).submatrix id fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j cc hc (e.symm i))
  frameTop : ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin c.T.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) c.T B.bT B.βT (FT.β.submatrix id e.symm)
  cg : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ
  cg_mid : ∀ j cc (H : j + 1 + cc = s), (ofSplit q).IsCombAt c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j)
    ((S.T (Fin D.R.t)).entry S.ψ ν j cc H 1 1)
  cg_pen : (ofSplit q).IsCombAt c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s)
    fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))
  cg_top : (ofSplit q).IsCombAt c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1))
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))

attribute [instance] GAt.fld GAt.val GAt.top GAt.loc GAt.mea GAt.bor

variable {B : Base c} {τ : ∀ j h, Matrix (Fin (c.bes j 0 h).L.rank) (Fin c.Lz.rank) D.host.E}

def GAt.Red {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt B τ PP) (x : G.S.P.J) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)) : Prop :=
  ∀ (a b : Fin D.R.k ⊕ Fin (G.s + 1)) (a' b' : Fin D.R.r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a →
    b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = g.val a' b' →
      valuation G.k ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E)) < 1

structure PinG (G : ∀ PP : B.Pg, GAt B τ PP.1) (cG : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ) : Prop where
  grp : ∀ g : ∀ PP : B.Pg, GL (Fin D.R.r) (Formalism.L2.DIV.kP PP.1), g ∈ B.P.H ↔ ∀ PP, ∃ x, (G PP).Red x (g PP)
  chr : ∀ (g : B.P.H) (x : ∀ PP, (G PP).S.P.J), (∀ PP, (G PP).Red (x PP) (g.1 PP)) → B.P.chi g = ∏ PP, (G PP).S.P.lam (x PP)
  prod : ∀ j, j < D.R.m → ∀ f, IsThetaFunO c.ψ _ _ f → comb c.ψ _ _ (cG j) f =
    B.Pg.attach.toList.foldr (fun PP f' => comb c.ψ _ _ ((G PP).cg j) f') f

end AtLevel

structure Reformulated (B : Base c) (t : Tup c) where

  Q : Finset (Formalism.L2.DIV.Pl D.host.E)

  μ : ℕ → ((AE D)ˣ →* Circle)
  η : (AE D)ˣ →* Circle
  cQ : ∀ j, t.Ch j → t.Ch (j + 1) → WO (c.X j) (c.X (j + 1)) →₀ ℂ
  eQ : ∀ j, t.Ch j → GA D (c.V j) →₀ ℂ
  eQT : ∀ n, n = D.R.m → t.Ch n → GA D c.T →₀ ℂ

open Classical in

def Reformulated.atQ {B : Base c} {t : Tup c} (w : Reformulated B t) (v : GlobalTheory.FinPl.Pl D) : Prop := ∃ PP ∈ w.Q, v = PP.under (𝓞 D.host.F)

open GlobalTheory.FinPl in

structure PinTup {B : Base c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (o : Off B k ι) {t : Tup c} (w : Reformulated B t) : Prop where
  offQ : ∀ v, w.atQ v → B.offS v ∧ ¬ o.atT v
  dd : ∀ j, j < D.R.m → ∀ α γ, CombAt w.atQ (w.cQ j α γ) ∧
    ∀ f, comb c.ψ _ _ (t.dd j α γ) f = comb c.ψ _ _ (w.cQ j α γ) (comb c.ψ _ _ (o.cG j) (comb c.ψ _ _ (o.cT j) f))
  e : ∀ j α, (∀ g ∈ (w.eQ j α).support, g ∈ grpAt (c.V j) w.atQ) ∧ t.e j α = (w.eQ j α).mapDomain (· * B.b j)
  eT : ∀ n h β, (∀ g ∈ (w.eQT n h β).support, g ∈ grpAt c.T w.atQ) ∧ t.eT n h β = (w.eQT n h β).mapDomain (· * B.bT)
  kom : ∀ j, j < D.R.m → IsWeilDatumO c.ψ _ _ (w.μ (j + 1)) (w.μ (j + 1)) (t.kom j)
  chBF : ∀ j ρ h, (t.sBF j ρ h).χV = w.μ (j + 1) * w.η⁻¹ ∧ (t.sBF j ρ h).χW = w.μ (j + 1)
  chFB : ∀ j σ h, (t.sFB j σ h).χV = w.μ (j + 1 + 1) ∧ (t.sFB j σ h).χW = w.μ (j + 1 + 1) * w.η⁻¹
  chT : ∀ j h, IsWeilDatumO c.ψ _ _ (w.μ (j + 1 + 1)) (w.μ (j + 1 + 1) * w.η⁻¹) (t.omT j h)
  unr : ∀ v, B.offS v → CharUnramAt D w.η v ∧ (¬ w.atQ v → ∀ j, 1 ≤ j → j ≤ D.R.m → CharUnramAt D (w.μ j) v)

end GlobalTheory.Fam

end
