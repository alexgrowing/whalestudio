import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

def trc {V : HSp D} (e : GA D V →₀ ℂ) (f : GA D V → ℂ) : GA D V → ℂ := ∑ g ∈ e.support, e g • rTrans g f

def Iter2 {G₁ G₂ : Type} [Group G₁] [MeasurableSpace G₁] [TopologicalSpace G₁] [Group G₂] [MeasurableSpace G₂] [TopologicalSpace G₂]
    {R₁ : Subgroup G₁} {R₂ : Subgroup G₂} (ρ₁ : Measure R₁) (μ₁ : Measure G₁) (ρ₂ : Measure R₂) (μ₂ : Measure G₂)
    (f : G₁ → G₂ → ℂ) (z : ℂ) : Prop :=
  ∃ f₁ : G₁ → ℂ, IsQuotIntL1 ρ₁ μ₁ f₁ z ∧ ∀ q, IsQuotIntL1 ρ₂ μ₂ (f q) (f₁ q)

set_option maxHeartbeats 2000000 in

structure Comm (D : D7) where
  θ : InfFam D
  ψ : AddChar (AF D.host.F) ℂ

  V : ℕ → HSp D
  par : ℕ → D.what₂.Tau → SPar
  M : ∀ j, DSModel (V j) (par j)
  T : HSp D
  parT : D.what₂.Tau → SPar
  MT : DSModel T parT
  It : ∀ j, PolF D (V (j + 1)).rank (V j).rank →ₗ[ℂ] SmT (M (j + 1)) →ₗ[ℂ] SmT (M j)
  ItT : ∀ j, j + 2 * 0 + 2 = D.R.m → PolF D T.rank (V (j + 1)).rank →ₗ[ℂ] SmT MT →ₗ[ℂ] SmT (M (j + 1))
  vol : ∀ j, Vol (V j)
  volT : Vol T

  X : ℕ → HSp D
  x : ∀ j, DefSp (X j)
  vac : ∀ j, WO (X j) (X (j + 1)) → ℂ
  bes : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (V j) (X j) ρ
  jac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → JacAt (V (j + 1)) (X (j + 1)) ρ
  lnk : ∀ j σ h, Link ((bes j (σ + 1) h).lev (x j).vol) (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ
  vL : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), VolM D (bes (j + 1 + 1) σ (idx_step h)).L.rank (X (j + 1)).rank
  Lz : HSp D
  oT : ∀ n, n = D.R.m → OrthDec (X n) T Lz

  μf : ∀ j, Measure (GfC (V j))
  ρJ : ∀ j ρ h, Measure ((jacGrp (jac j ρ h).d).subgroupOf (GfC (V (j + 1))))
  ρB : ∀ j ρ h, Measure ((besGrp (bes j ρ h).d (bes j ρ h).o).subgroupOf (GfC (V j)))

  Fr : ℕ → Type

abbrev Comm.B (c : Comm D) (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) : BesLev D ρ := (c.bes j ρ h).lev (c.x j).vol

abbrev Comm.J (c : Comm D) (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) : JacLev D ρ := (c.jac j ρ h).lev (c.x (j + 1)).vol

def Comm.IsReal (c : Comm D) (j : ℕ) (C : WO (c.X j) (c.X (j + 1)) → WO (c.X (j + 1)) (c.X (j + 1 + 1)) → ℂ) : Prop :=
  IsBiVac c.ψ _ _ _ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L C ∧ IsBiSmooth C

structure Comm.Is (c : Comm D) : Prop where
  std : IsStdChar D c.ψ (-1)
  inf : IsInfFam c.θ
  x : ∀ j, j ≤ D.R.m → (c.x j).Is
  cpt : CoCpt c.T
  μf : ∀ j, (c.μf j).IsHaarMeasure
  ρJ : ∀ j ρ h, (c.ρJ j ρ h).IsHaarMeasure
  ρB : ∀ j ρ h, (c.ρB j ρ h).IsHaarMeasure
  span : ∀ j, j + 1 < D.R.m → GlobalTheory.Core.Mi.ItSpans (c.M j) (c.M (j + 1)) (c.It j)
  spanT : ∀ j h, GlobalTheory.Core.Mi.ItSpans (c.M (j + 1)) c.MT (c.ItT j h)

set_option maxHeartbeats 2000000 in

structure Tup (c : Comm D) where
  om : ∀ j, Om (c.V j) (c.V (j + 1))
  omT : ∀ j, j + 2 * 0 + 2 = D.R.m → Om (c.V (j + 1)) c.T
  pt : ∀ j, PolF D (c.V (j + 1)).rank (c.V j).rank → WO (c.V j) (c.V (j + 1)) → ℂ
  ptT : ∀ j, j + 2 * 0 + 2 = D.R.m → PolF D c.T.rank (c.V (j + 1)).rank → WO (c.V (j + 1)) c.T → ℂ
  sBF : ∀ j ρ h, StepBF c.ψ (c.B j ρ h) (c.J j ρ h)
  sFB : ∀ j σ h, StepFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))

  CC : ∀ j, Submodule ℂ (SmT (c.M j) →ₗ[ℂ] (GA D (c.V j) → ℂ))
  CT : Submodule ℂ (SmT c.MT →ₗ[ℂ] (GA D c.T → ℂ))
  io : ∀ j, CC (j + 1) →ₗ[ℂ] CC j
  ioT : ∀ j, j + 2 * 0 + 2 = D.R.m → CT →ₗ[ℂ] CC (j + 1)

  kom : ∀ j, Om (c.X j) (c.X (j + 1))
  Ch : ℕ → Type
  [fin : ∀ j, Fintype (Ch j)]
  dd : ∀ j, Ch j → Ch (j + 1) → WO (c.X j) (c.X (j + 1)) →₀ ℂ
  e : ∀ j, Ch j → GA D (c.V j) →₀ ℂ
  eT : ∀ n, n = D.R.m → Ch n → GA D c.T →₀ ℂ

  Col : ℕ → Type
  Ram : ∀ j, Set (Col j)
  S : ∀ j, Col j → Col j
  K : ∀ j, Col j → Col (j + 1)
  rd : ∀ j, Ch j → Col j → c.Fr j → GA D (c.X j) → ℂ
  tail : ∀ n, n = D.R.m → Col n → CT → ℂ

  cI : ℕ → ℂ
  cV : ℕ → ℂ
  cK : ℕ → ℂ
  cP : ℂ

attribute [instance] Tup.fin

namespace Tup

variable {c : Comm D} (t : Tup c)

def ker (j : ℕ) (α : t.Ch j) (γ : t.Ch (j + 1)) : KerDat (c.X j) (c.X (j + 1)) := ⟨t.kom j, c.vac j, t.dd j α γ⟩

def perF (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) (φ : t.Ch j → GA D (c.X j) → ℂ) (f : GA D (c.V j) → ℂ) : ℂ :=
  ∑ α, (c.B j ρ h).per c.ψ (φ α) (trc (t.e j α) f)

def per (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) (ψ : t.Col j) (G : t.CC j) (y : c.Fr j) (v : SmT (c.M j)) : ℂ :=
  t.perF j ρ h (fun α => t.rd j α ψ y) (G.1 v)

def two (j : ℕ) (φ : t.Ch j → GA D (c.X j) → ℂ)
    (C : WO (c.X j) (c.X (j + 1)) → WO (c.X (j + 1)) (c.X (j + 1 + 1)) → ℂ) (β : t.Ch (j + 1 + 1)) : GA D (c.X (j + 1 + 1)) → ℂ :=
  ∑ α, ∑ γ, biLift (t.kom j) (t.kom (j + 1)) (c.x j).vol (c.x (j + 1)).vol (φ α)
    (biComb c.ψ _ _ _ (t.dd j α γ) (t.dd (j + 1) γ β) C)

def integrand (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (P₁ : PolF D (c.V (j + 1)).rank (c.V j).rank)
    (P₂ : PolF D (c.V (j + 1 + 1)).rank (c.V (j + 1)).rank) (φ : t.Ch j → GA D (c.X j) → ℂ) (f : GA D (c.V (j + 1 + 1)) → ℂ)
    (h₁ : GA D (c.V (j + 1))) (h₂ : GA D (c.V (j + 1 + 1))) : ℂ :=
  ∑ α, ∑ g ∈ (t.e j α).support, t.e j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
    (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (t.pt j P₁) (t.pt (j + 1) P₂) (φ α) g h₁ h₂)
    (rTrans h₂ f)

def perT (n : ℕ) (h : n = D.R.m) (φ : t.Ch n → GA D (c.X n) → ℂ) (f : GA D c.T → ℂ) : ℂ :=
  ∑ β, ∫ h' in c.volT.𝓕, trc (t.eT n h β) f h' * φ β ((c.oT n h).emb (h', 1)) ∂c.volT.μ

structure Is : Prop where
  sBF : ∀ j ρ h, (t.sBF j ρ h).om = t.om j ∧ (t.sBF j ρ h).vW = c.vol (j + 1)
  sFB : ∀ j σ h, (t.sFB j σ h).om = t.om (j + 1) ∧ (t.sFB j σ h).vW = c.vol (j + 1 + 1)
  pt : ∀ j, j + 1 < D.R.m → ∀ P, IsThetaFunO c.ψ _ _ (t.pt j P)
  ptT : ∀ j h P, IsThetaFunO c.ψ _ _ (t.ptT j h P)
  CC : ∀ j, j < D.R.m → ∃ J χ, t.CC j ≤ MultT c.θ (c.M j) J χ
  CT : ∃ J χ, t.CT ≤ MultT c.θ c.MT J χ
  io : ∀ j, j + 1 < D.R.m → ∀ (G : t.CC (j + 1)) P v,
    liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (G.1 v) (t.pt j P) = t.cI j • (t.io j G).1 (c.It j P v)
  ioT : ∀ j h (F : t.CT) P v,
    liftS (t.omT j h) c.volT.μ c.volT.𝓕 (F.1 v) (t.ptT j h P) = t.cI (j + 1) • (t.ioT j h F).1 (c.ItT j h P v)
  cI : ∀ j, j < D.R.m → t.cI j ≠ 0
  ker : ∀ j, j < D.R.m → ∀ α γ, (t.ker j α γ).Is c.ψ c.θ (c.x j) (c.x (j + 1))
  e : ∀ j α, ∀ g ∈ (t.e j α).support, g ∈ GfC (c.V j)
  eT : ∀ n h β, ∀ g ∈ (t.eT n h β).support, g ∈ GfC c.T
  stabK : ∀ j, j < D.R.m → ∀ ψ ∈ t.Ram j, t.K j ψ ∈ t.Ram (j + 1)
  stabS : ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram j, t.S j ψ ∈ t.Ram j

def LocFin : Prop :=
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂, ∃ (K₁ : Subgroup (GA D (c.V (j + 1)))) (T₁ : Finset (GA D (c.V (j + 1)))),
    K₁ ≤ GfC _ ∧ IsCompact (K₁ : Set (GA D (c.V (j + 1)))) ∧ IsOpen ((K₁.subgroupOf (GfC _) : Subgroup (GfC (c.V (j + 1)))) : Set (GfC (c.V (j + 1)))) ∧
    (∀ q ∈ T₁, q ∈ GfC _) ∧
    (∀ k ∈ K₁, ∃ a : ℂ, a ≠ 0 ∧ t.om j (1, k) (t.pt j P₁) = a⁻¹ • t.pt j P₁ ∧ t.om (j + 1) (k, 1) (t.pt (j + 1) P₂) = a • t.pt (j + 1) P₂) ∧
    ∀ α, ∀ g ∈ (t.e j α).support, ∀ h₁, flatBF (t.sBF j (σ + 1) h) (t.om j (g, h₁) (t.pt j P₁)) ≠ 0 →
      ∃ q ∈ T₁, InCell (jacGrp (c.jac j (σ + 1) h).d) q K₁ h₁

def up (i : ℕ) (ψ : t.Col 0) : t.Col (2 * i) :=
  Nat.rec (motive := fun i => t.Col (2 * i)) ψ (fun i φ => t.K (2 * i + 1) (t.K (2 * i) (t.S (2 * i) φ))) i

def dn (j : ℕ) : t.CC j →ₗ[ℂ] t.CC 0 :=
  Nat.rec (motive := fun j => t.CC j →ₗ[ℂ] t.CC 0) LinearMap.id (fun j f => f ∘ₗ t.io j) j

def cTop (n : ℕ) : ℂ := (∏ i ∈ Finset.range n, t.cV (2 * i) * t.cK (2 * i) * t.cK (2 * i + 1)) * t.cP

def cBot : ℂ := ∏ j ∈ Finset.range D.R.m, t.cI j

end Tup

section Laws

variable {c : Comm D} {𝒯 : Type} (t : 𝒯 → Tup c)

def RealEq : Prop :=
  ∀ j, j < D.R.m → ∀ s s', ∀ a ∈ GinfC (c.X j), ∀ b ∈ GinfC (c.X (j + 1)), ∀ f, IsThetaFunO c.ψ _ _ f →
    (t s).kom j (a, b) f = (t s').kom j (a, b) f

def ValX : Prop :=
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂, ∀ a ∈ GinfC (c.V (j + 1)), ∀ a' ∈ GinfC (c.V (j + 1 + 1)),
    ∃ C, c.IsReal j C ∧ ∀ s, ∀ ψ ∈ (t s).Ram j, ∀ y (G : (t s).CC (j + 1 + 1)) v,
      Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
        (fun q₁ q₂ => (t s).integrand j σ h P₁ P₂ (fun α => (t s).rd j α ψ y) (G.1 v) (a * q₁.1) (a' * q₂.1))
        ((t s).cV j * (t s).perF (j + 1 + 1) σ (idx_step h) ((t s).two j (fun α => (t s).rd j α ((t s).S j ψ) y) C)
          (rTrans a' (G.1 v)))

def ValLastX : Prop :=
  ∀ j (h : j + 2 * 0 + 2 = D.R.m) P₁ P₂, ∃ C, c.IsReal j C ∧ ∀ s, ∀ ψ ∈ (t s).Ram j, ∀ y (F : (t s).CT) v,
    (t s).perF j 0 h (fun α => (t s).rd j α ψ y) (liftS ((t s).om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
        (liftS ((t s).omT j h) c.volT.μ c.volT.𝓕 (F.1 v) ((t s).ptT j h P₂)) ((t s).pt j P₁)) =
      (t s).cV j * (t s).perT (j + 1 + 1) h ((t s).two j (fun α => (t s).rd j α ((t s).S j ψ) y) C) (F.1 v)

def KerX : Prop :=
  ∀ j, j < D.R.m → ∀ y P, ∃ a : c.Fr (j + 1) →₀ ℂ, ∀ s, ∀ ψ ∈ (t s).Ram j, ∀ γ,
    ∑ α, ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) P ((t s).rd j α ψ y) =
      (t s).cK j • ∑ y' ∈ a.support, a y' • (t s).rd (j + 1) γ ((t s).K j ψ) y'

def PerX : Prop :=
  ∀ n (h : n = D.R.m) y v, ∃ a : ℂ, ∀ s, ∀ ψ ∈ (t s).Ram n, ∀ F : (t s).CT,
    (t s).perT n h (fun β => (t s).rd n β ψ y) (F.1 v) = (t s).cP * a * (t s).tail n h ψ F

def RdX : Prop :=
  ∀ j, j ≤ D.R.m → ∃ χ, ∀ s, ∀ ψ ∈ (t s).Ram j, ∀ α y, IsContAut (c.X j) ((t s).rd j α ψ y) ∧ HasCen (c.X j) χ ((t s).rd j α ψ y)

structure LawsX : Prop where
  com : c.Is
  tup : ∀ s, (t s).Is
  loc : ∀ s, (t s).LocFin
  real : RealEq t
  val : ValX t
  last : ValLastX t
  ker : KerX t
  per : PerX t
  rd : RdX t

def TwoX : Prop :=
  ∀ j, j + 2 ≤ D.R.m → ∀ C, c.IsReal j C → ∀ y, ∃ a : c.Fr (j + 1 + 1) →₀ ℂ, ∀ s, ∀ ψ ∈ (t s).Ram j, ∀ β,
    (t s).two j (fun α => (t s).rd j α ψ y) C β =
      ((t s).cK j * (t s).cK (j + 1)) • ∑ y' ∈ a.support, a y' • (t s).rd (j + 1 + 1) β ((t s).K (j + 1) ((t s).K j ψ)) y'

def StepX : Prop :=
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) (I : Type) [Fintype I] (s : I → 𝒯) (α : I → ℂ) (ψ : ∀ i, (t (s i)).Col j)
    (G : ∀ i, (t (s i)).CC (j + 1 + 1)), (∀ i, ψ i ∈ (t (s i)).Ram j) →
    (∀ y v, ∑ i, α i * ((t (s i)).cV j * (t (s i)).cK j * (t (s i)).cK (j + 1)) * (t (s i)).per (j + 1 + 1) σ (idx_step h)
      ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) (G i) y v = 0) →
    ∀ y v, ∑ i, α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)) *
      (t (s i)).per j (σ + 1) h (ψ i) ((t (s i)).io j ((t (s i)).io (j + 1) (G i))) y v = 0

def LastX : Prop :=
  ∀ j (h : j + 2 * 0 + 2 = D.R.m) (I : Type) [Fintype I] (s : I → 𝒯) (α : I → ℂ) (ψ : ∀ i, (t (s i)).Col j)
    (F : ∀ i, (t (s i)).CT), (∀ i, ψ i ∈ (t (s i)).Ram j) →
    ∑ i, α i * ((t (s i)).cV j * (t (s i)).cK j * (t (s i)).cK (j + 1) * (t (s i)).cP) * (t (s i)).tail (j + 1 + 1) h
      ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) (F i) = 0 →
    ∀ y v, ∑ i, α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)) *
      (t (s i)).per j 0 h (ψ i) ((t (s i)).io j ((t (s i)).ioT j h (F i))) y v = 0

def MainX : Prop :=
  ∀ n (h : 2 * n + 2 * 0 + 2 = D.R.m) (h₀ : 0 + 2 * n + 2 = D.R.m) (I : Type) [Fintype I] (s : I → 𝒯) (α : I → ℂ)
    (ψ : ∀ i, (t (s i)).Col 0) (F : ∀ i, (t (s i)).CT), (∀ i, ψ i ∈ (t (s i)).Ram 0) →
    ∑ i, α i * (t (s i)).cTop (n + 1) * (t (s i)).tail (2 * (n + 1)) h ((t (s i)).up (n + 1) (ψ i)) (F i) = 0 →
    ∀ y v, ∑ i, α i * (t (s i)).cBot *
      (t (s i)).per 0 n h₀ (ψ i) ((t (s i)).dn (2 * n + 1) ((t (s i)).ioT (2 * n) h (F i))) y v = 0

end Laws

end GlobalTheory.SeeSaw

end
