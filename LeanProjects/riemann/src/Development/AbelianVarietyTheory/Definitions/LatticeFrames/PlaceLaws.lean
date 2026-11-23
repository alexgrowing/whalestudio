import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl

namespace GlobalTheory.SeeSaw

variable {D : D7}

structure BiOp (A S A' : HSp D) where
  n : ℕ
  u : Fin n → WO A S →₀ ℂ
  u' : Fin n → WO S A' →₀ ℂ

def BiOp.app (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (o : BiOp A S A') (C : WO A S → WO S A' → ℂ) :
    WO A S → WO S A' → ℂ := ∑ i, biComb ψ A S A' (o.u i) (o.u' i) C

def IsNormAt (V : HSp D) (R : Subgroup (GA D V)) (L : Lat V) (P : Pl D → Prop) (ρ : Measure (R.subgroupOf (grpAt V P)))
    (μ : Measure (grpAt V P)) : Prop :=
  μ.IsHaarMeasure ∧ ρ.IsHaarMeasure ∧ μ {g | InK V L P g.1} = 1 ∧ ρ {g | InK V L P g.1.1} = 1

namespace Comm

variable (c : Comm D)

abbrev bl (j : ℕ) (oma : Om (c.X j) (c.X (j + 1))) (omb : Om (c.X (j + 1)) (c.X (j + 1 + 1))) :=
  biLift oma omb (c.x j).vol (c.x (j + 1)).vol

def ctr (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (s₁ : StepBF c.ψ (c.B j (σ + 1) h) (c.J j (σ + 1) h))
    (s₂ : StepFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))) (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ)
    (Ψ₂ : WO (c.V (j + 1)) (c.V (j + 1 + 1)) → ℂ) : WO (c.X j) (c.X (j + 1)) → WO (c.X (j + 1)) (c.X (j + 1 + 1)) → ℂ :=
  GlobalTheory.Unf.contr (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) (flatBF s₁ Ψ₁) (flatFB s₂ Ψ₂)

def lst (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (τ : Matrix (Fin (c.bes j 0 h).L.rank) (Fin c.Lz.rank) D.host.E)
    (s₁ : StepBF c.ψ (c.B j 0 h) (c.J j 0 h)) (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) c.T → ℂ) :
    WO (c.X j) (c.X (j + 1)) → WO (c.X (j + 1)) (c.X (j + 1 + 1)) → ℂ :=
  lastBi (c.bes j 0 h).o (c.oT (j + 1 + 1) h) τ (flatBF s₁ Ψ₁) fun w => Ψ₂ ((c.jac j 0 h).d.ext0 c.T w)

end Comm

set_option maxHeartbeats 1000000 in

structure VCom (c : Comm D) where

  gP : Finset (Pl D)
  tP : Finset (Pl D)

  N : ∀ j, Lat (c.V j)
  NT : Lat c.T
  b : ∀ j, GA D (c.V j)
  bT : GA D c.T

  Ψ : ∀ j, PolF D (c.V (j + 1)).rank (c.V j).rank → GA D (c.V j) → GA D (c.V (j + 1)) → WO (c.V j) (c.V (j + 1)) → ℂ
  ΨT : ∀ j, j + 2 * 0 + 2 = D.R.m → PolF D c.T.rank (c.V (j + 1)).rank → WO (c.V (j + 1)) c.T → ℂ
  τ : ∀ j (h : j + 2 * 0 + 2 = D.R.m), Matrix (Fin (c.bes j 0 h).L.rank) (Fin c.Lz.rank) D.host.E

  JG : ∀ j, Subgroup (GA D (c.V j))
  eG : ∀ j, WO (c.V j) (c.V (j + 1)) →₀ ℂ
  eGT : ∀ j, j + 2 * 0 + 2 = D.R.m → WO (c.V (j + 1)) c.T →₀ ℂ
  dG : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ
  cG : ℕ → ℂ

  RamAd : ∀ j, Set (GA D (c.X j) → ℂ)
  Sad : ∀ j, (GA D (c.X j) → ℂ) → GA D (c.X j) → ℂ
  dT : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ
  op : ∀ j, BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))

structure VTup {c : Comm D} (t : Tup c) where

  Q : Finset (Pl D)

  sc : ℕ → ℂ
  eQ : ∀ j, WO (c.V j) (c.V (j + 1)) →₀ ℂ
  eQT : ∀ j, j + 2 * 0 + 2 = D.R.m → WO (c.V (j + 1)) c.T →₀ ℂ
  dQ : ∀ j, t.Ch j → t.Ch (j + 1) → WO (c.X j) (c.X (j + 1)) →₀ ℂ
  ε : ∀ j, t.Ch j → GA D (c.V j) →₀ ℂ
  εT : ∀ n, n = D.R.m → t.Ch n → GA D c.T →₀ ℂ

  FX : ∀ j, t.Ch j → Set (GA D (c.X j) → ℂ)
  FY : ∀ j, Set (GA D (c.V j) → ℂ)
  FT : Set (GA D c.T → ℂ)
  cQ : ℕ → ℂ
  cT : ℕ → ℂ

variable {c : Comm D} (v : VCom c)

namespace VCom

def K (j : ℕ) : Set (GA D (c.V j)) := {g | ∃ κ, InK (c.V j) (v.N j) (· ∉ v.gP) κ ∧ ∃ k ∈ v.JG j, g = κ * k}

def vr (j : ℕ) (R : Subgroup (GA D (c.V j))) (ρ : Measure (R.subgroupOf (GfC (c.V j)))) : ℂ :=
  (((c.μf j).real {g | g.1 ∈ v.K j} / ρ.real {g | g.1.1 ∈ v.K j} : ℝ) : ℂ)

def kap (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) : ℂ :=
  v.vr (j + 1) _ (c.ρJ j (σ + 1) h) * v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h))

structure Is : Prop where
  disj : Disjoint v.gP v.tP
  sd : ∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j)
  sdT : IsSelfDualC c.T v.NT
  b : ∀ j, v.b j ∈ GfC (c.V j)
  bT : v.bT ∈ GfC c.T
  Ψ : ∀ j, j + 1 < D.R.m → ∀ P, ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) (v.Ψ j P a a')
  ΨT : ∀ j h P, Vac c.ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) (v.ΨT j h P)
  JG : ∀ j, j < D.R.m → v.JG j ≤ grpAt (c.V j) (· ∈ v.gP) ∧ IsCompact (v.JG j : Set (GA D (c.V j))) ∧
    IsOpen (((v.JG j).subgroupOf (grpAt (c.V j) (· ∈ v.gP)) : Subgroup _) : Set (grpAt (c.V j) (· ∈ v.gP)))
  atG : ∀ j, CombAt (· ∈ v.gP) (v.eG j) ∧ CombAt (· ∈ v.gP) (v.dG j) ∧ ∀ h, CombAt (· ∈ v.gP) (v.eGT j h)
  atT : ∀ j, CombAt (· ∈ v.tP) (v.dT j) ∧ ∀ i, CombAt (· ∈ v.tP) ((v.op j).u i) ∧ CombAt (· ∈ v.tP) ((v.op j).u' i)
  ram : ∀ j, ∀ φ ∈ v.RamAd j, IsContAut (c.X j) φ ∧ v.Sad j φ ∈ v.RamAd j

end VCom

section One

variable {t : Tup c} (w : VTup t)

def offP (p : Pl D) : Prop := p ∉ v.gP ∧ p ∉ w.Q

structure VForm : Prop where
  disjG : Disjoint w.Q v.gP
  disjT : Disjoint w.Q v.tP
  vf : ∀ j, j + 1 < D.R.m → ∀ P, ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, t.om j (a * v.b j, a' * v.b (j + 1)) (t.pt j P) =
    w.sc j • comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) (v.Ψ j P a a'))
  vfT : ∀ j h P, t.omT j h (v.b (j + 1), v.bT) (t.ptT j h P) =
    w.sc (j + 1) • comb c.ψ _ _ (v.eGT j h) (comb c.ψ _ _ (w.eQT j h) (v.ΨT j h P))
  atQ : ∀ j, CombAt (· ∈ w.Q) (w.eQ j) ∧ (∀ h, CombAt (· ∈ w.Q) (w.eQT j h)) ∧ ∀ α γ, CombAt (· ∈ w.Q) (w.dQ j α γ)
  e : ∀ j α, t.e j α = (w.ε j α).mapDomain (· * v.b j) ∧ ∀ g ∈ (w.ε j α).support, g ∈ grpAt (c.V j) (· ∈ w.Q)
  eT : ∀ n h β, t.eT n h β = (w.εT n h β).mapDomain (· * v.bT) ∧ ∀ g ∈ (w.εT n h β).support, g ∈ grpAt c.T (· ∈ w.Q)
  dd : ∀ j, j < D.R.m → ∀ α γ f, IsThetaFunO c.ψ _ _ f →
    comb c.ψ _ _ (t.dd j α γ) f = comb c.ψ _ _ (w.dQ j α γ) (comb c.ψ _ _ (v.dG j) (comb c.ψ _ _ (v.dT j) f))
  rd : ∀ j, j + 2 ≤ D.R.m → ∀ ψ ∈ t.Ram j, ∀ α y, t.rd j α ψ y ∈ v.RamAd j ∧ t.rd j α ψ y ∈ w.FX j α ∧
    t.rd j α (t.S j ψ) y = v.Sad j (t.rd j α ψ y)
  row : ∀ j, j < D.R.m → ∀ (G : t.CC j) x, ∀ a ∈ GinfC _, rTrans (a * v.b j) (G.1 x) ∈ w.FY j ∧
    ∀ κ, InK (c.V j) (v.N j) (offP v w) κ → rTrans κ (rTrans (a * v.b j) (G.1 x)) = rTrans (a * v.b j) (G.1 x)
  rowT : ∀ (F : t.CT) x, rTrans v.bT (F.1 x) ∈ w.FT

  lawG : ∀ j, j + 1 < D.R.m → ∀ k ∈ v.JG (j + 1), ∃ a : ℂ, a ≠ 0 ∧
    (∀ f, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) f →
      t.om j (1, k) (comb c.ψ _ _ (v.eG j) f) = a⁻¹ • comb c.ψ _ _ (v.eG j) f) ∧
    (j + 1 + 1 < D.R.m → ∀ f, Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) f →
      t.om (j + 1) (k, 1) (comb c.ψ _ _ (v.eG (j + 1)) f) = a • comb c.ψ _ _ (v.eG (j + 1)) f) ∧
    ∀ (G : t.CC (j + 1)) x, rTrans k (rTrans (v.b (j + 1)) (G.1 x)) = a • rTrans (v.b (j + 1)) (G.1 x)

structure WeilOK : Prop where
  mid : ∀ j σ h, ∃ (χA χA' χz : (AE D)ˣ →* Circle) (omz : Om (c.bes j (σ + 1) h).L (c.X (j + 1)))
    (omz' : Om (c.X (j + 1)) (c.bes (j + 1 + 1) σ (idx_step h)).L),
    (t.sBF j (σ + 1) h).χV = χA * χz ∧ (t.sFB j σ h).χW = χA' * χz ∧
    IsWeilDatumO c.ψ _ _ χA (t.sBF j (σ + 1) h).χW (t.kom j) ∧ IsWeilDatumO c.ψ _ _ χz (t.sBF j (σ + 1) h).χW omz ∧
    IsWeilDatumO c.ψ _ _ (t.sFB j σ h).χV χA' (t.kom (j + 1)) ∧ IsWeilDatumO c.ψ _ _ (t.sFB j σ h).χV χz omz'
  last : ∀ j h, ∃ (χA χz χS' χT : (AE D)ˣ →* Circle) (omz : Om (c.bes j 0 h).L (c.X (j + 1)))
    (omT : Om (c.X (j + 1)) c.T) (omz'' : Om (c.X (j + 1)) c.Lz),
    (t.sBF j 0 h).χV = χA * χz ∧ IsWeilDatumO c.ψ _ _ χA (t.sBF j 0 h).χW (t.kom j) ∧
    IsWeilDatumO c.ψ _ _ χz (t.sBF j 0 h).χW omz ∧ IsWeilDatumO c.ψ _ _ χS' (χT * χz⁻¹) (t.kom (j + 1)) ∧
    IsWeilDatumO c.ψ _ _ χS' χT omT ∧ IsWeilDatumO c.ψ _ _ χS' χT (t.omT j h) ∧ IsWeilDatumO c.ψ _ _ χS' χz⁻¹ omz''
  tau : ∀ j h, c.Lz.rank = 1 ∧
    (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram

def OffLaw : Prop :=
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Φ₁ Φ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (offP v w) Φ₁ →
    Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (offP v w) Φ₂ →
    (∀ κ, InK _ (v.N (j + 1)) (offP v w) κ → t.om j (1, κ) Φ₁ = Φ₁ ∧ t.om (j + 1) (κ, 1) Φ₂ = Φ₂) ∧
    (∀ κ, InK _ (v.N (j + 1 + 1)) (offP v w) κ → t.om (j + 1) (1, κ) Φ₂ = Φ₂) ∧
    (∀ h₁, flatBF (t.sBF j (σ + 1) h) (t.om j (1, h₁) Φ₁) ≠ 0 →
      InBig _ (jacGrp (c.jac j (σ + 1) h).d) (v.N (j + 1)) (offP v w) h₁) ∧
    ∀ φ ∈ v.RamAd j, ∀ h₂,
      Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) Φ₁ Φ₂ φ 1 1 h₂ ≠ 0 →
        InBig _ (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o) (v.N (j + 1 + 1)) (offP v w) h₂

def GSupp : Prop :=
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ₁ →
    Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) Ψ₂ →
    (∀ x ∈ grpAt _ (· ∈ v.gP), flatBF (t.sBF j (σ + 1) h) (t.om j (1, x) (comb c.ψ _ _ (v.eG j) Ψ₁)) ≠ 0 →
      ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ grpAt _ (· ∈ v.gP) ∧ ∃ k ∈ v.JG (j + 1), x = r * k) ∧
    ∀ x ∈ grpAt _ (· ∈ v.gP), c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (v.eG j) Ψ₁)
        (t.om (j + 1) (1, x) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂)) ≠ 0 →
      ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, r ∈ grpAt _ (· ∈ v.gP) ∧
        ∃ k ∈ v.JG (j + 1 + 1), x = r * k

def GValue : Prop :=
  (∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ₁ →
    Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) Ψ₂ →
    c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂) =
      v.cG j • biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) ∧
  ∀ j (h : j + 2 * 0 + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ₁ →
    Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.gP) Ψ₂ →
    c.lst j h (v.τ j h) (t.sBF j 0 h) (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eGT j h) Ψ₂) =
      v.cG j • biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)

def VacLaw : Prop :=
  (∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∉ v.tP) Ψ₁ →
    Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∉ v.tP) Ψ₂ →
    BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∉ v.tP) (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) ∧
  ∀ j (h : j + 2 * 0 + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∉ v.tP) Ψ₁ →
    Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∉ v.tP) Ψ₂ →
    BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∉ v.tP) (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)

def TLaw : Prop :=
  (∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ →
    Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.tP) Ψ₂ →
    BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP)
      ((v.op j).app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) ∧
    ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ v.RamAd j,
      c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) =
        w.cT j • c.bl j (t.kom j) (t.kom (j + 1)) (v.Sad j φ) (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1))
          ((v.op j).app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂))))) ∧
  ∀ j (h : j + 2 * 0 + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ →
    Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.tP) Ψ₂ →
    BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP)
      ((v.op j).app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ∧
    ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ v.RamAd j, ∀ f, IsContAut c.T f →
      (∀ κ, InK c.T v.NT (· ∈ v.tP) κ → rTrans κ f = f) →
      ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂))
          ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ =
        w.cT j * ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) (v.Sad j φ) (biComb c.ψ _ _ _ d d'
          (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) ((v.op j).app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂))))
          ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ

def QLaw : Prop :=
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) ρ₁ μ₁ ρ₂ μ₂,
    IsNormAt (c.V (j + 1)) (jacGrp (c.jac j (σ + 1) h).d) (v.N (j + 1)) (· ∈ w.Q) ρ₁ μ₁ →
    IsNormAt (c.V (j + 1 + 1)) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o)
      (v.N (j + 1 + 1)) (· ∈ w.Q) ρ₂ μ₂ →
    ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ →
    ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, IsContAut _ (φ α) ∧ φ α ∈ w.FX j α) → ∀ f, IsAutFun _ f → f ∈ w.FY (j + 1 + 1) →
      Iter2 ρ₁ μ₁ ρ₂ μ₂
        (fun q₁ q₂ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
          (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (w.eQ j) Ψ₁)
            (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f))
        (w.cQ j * ∑ β, (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
          (∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β)
            (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂))) (trc (w.ε (j + 1 + 1) β) f))

def QLast : Prop :=
  ∀ j (h : j + 2 * 0 + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ w.Q) Ψ₂ →
    ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, IsContAut _ (φ α) ∧ φ α ∈ w.FX j α) → ∀ f, IsAutFun _ f → f ∈ w.FT →
      ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) (φ α)
          (c.lst j h (v.τ j h) (t.sBF j 0 h) (t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (w.eQT j h) Ψ₂))
          ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ =
        w.cQ j * ∑ β, ∫ h' in c.volT.𝓕, trc (w.εT (j + 1 + 1) h β) f h' *
          (∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β)
            (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂))) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ

def QFin : Prop :=
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ (K₁ : Subgroup (GA D (c.V (j + 1)))) (T₁ : Finset (GA D (c.V (j + 1)))),
    K₁ ≤ grpAt _ (· ∈ w.Q) ∧ IsCompact (K₁ : Set (GA D (c.V (j + 1)))) ∧
    IsOpen ((K₁.subgroupOf (grpAt _ (· ∈ w.Q)) : Subgroup _) : Set (grpAt (c.V (j + 1)) (· ∈ w.Q))) ∧
    (∀ q ∈ T₁, q ∈ grpAt _ (· ∈ w.Q)) ∧
    (∀ k ∈ K₁, ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ →
      Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ →
      t.om j (1, k) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧
        t.om (j + 1) (k, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) = a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) ∧
    ∀ Ψ₁, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∀ α, ∀ g ∈ (w.ε j α).support, ∀ x ∈ grpAt _ (· ∈ w.Q),
      flatBF (t.sBF j (σ + 1) h) (t.om j (g, x) (comb c.ψ _ _ (w.eQ j) Ψ₁)) ≠ 0 →
        ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ grpAt _ (· ∈ w.Q) ∧ ∃ q ∈ T₁, ∃ k ∈ K₁, x = r * q * k

def CVEq : Prop :=
  (∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), t.cV j = v.kap j σ h * (w.sc j * w.sc (j + 1)) * w.cQ j * v.cG j * w.cT j) ∧
    ∀ j (_ : j + 2 * 0 + 2 = D.R.m), t.cV j = (w.sc j * w.sc (j + 1)) * w.cQ j * v.cG j * w.cT j

def TopSph : Prop := ∀ (F : t.CT) x κ, InK c.T v.NT (· ∈ v.tP) κ → rTrans κ (rTrans v.bT (F.1 x)) = rTrans v.bT (F.1 x)

structure PlaceLaws : Prop where
  form : VForm v w
  weil : WeilOK (t := t) v
  off : OffLaw v w
  gs : GSupp (t := t) v
  gv : GValue (t := t) v
  vac : VacLaw (t := t) v
  tl : TLaw v w
  ql : QLaw v w
  qlast : QLast v w
  qfin : QFin v w
  cv : CVEq v w
  sph : TopSph (t := t) v

end One

end GlobalTheory.SeeSaw

end
