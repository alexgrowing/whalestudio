import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

def comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) : WO S T → ℂ :=
  ∑ u ∈ c.support, c u • heisO ψ S T u f

def IsFinComb {S T : HSp D} (c : WO S T →₀ ℂ) : Prop := ∀ u ∈ c.support, u.map (infPart D) = 0

def biComb (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => comb ψ A S c (fun u' => comb ψ S A' c' (C u') v) u

structure IsBiVac (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (LA : Set (Fin A.rank → D.host.E))
    (LS : Set (Fin S.rank → D.host.E)) (LA' : Set (Fin A'.rank → D.host.E)) (C : WO A S → WO S A' → ℂ) : Prop where
  cont : Continuous fun p : WO A S × WO S A' => C p.1 p.2
  left : ∀ v, IsThetaFunO ψ A S (fun u => C u v) ∧ IsLatVac (heisO ψ A S) (latO A S LA LS fun _ => True) fun u => C u v
  right : ∀ u, IsThetaFunO ψ S A' (C u) ∧ IsLatVac (heisO ψ S A') (latO S A' LS LA' fun _ => True) (C u)

def JointSmooth {A S A' : HSp D} (C : WO A S → WO S A' → ℂ) : Prop :=
  ∀ (n : ℕ) (L : (Fin n → ℝ) →+ WO A S) (L' : (Fin n → ℝ) →+ WO S A'), Continuous L → Continuous L' →
    (∀ t, (L t).map (finPart D) = 0) → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ u v, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => C (u + L t) (v + L' t)

def biLift {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ)
    (C : WO A S → WO S A' → ℂ) (h₂ : GA D A') : ℂ :=
  ∫ h₁ in vS.𝓕, (∫ h₀ in vA.𝓕, φ h₀ * omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0 ∂vA.μ) ∂vS.μ

def HasCen (A : HSp D) (χ : GA D A → ℂ) (φ : GA D A → ℂ) : Prop :=
  ∀ z ∈ GinfC A, z ∈ Subgroup.center (GA D A) → ∀ h, φ (h * z) = χ z * φ h

def InCell {V : HSp D} (R : Subgroup (GA D V)) (t : GA D V) (J : Set (GA D V)) (h : GA D V) : Prop :=
  ∃ r ∈ R, ∃ a ∈ GinfC V, ∃ k ∈ J, h = r * a * t * k

structure DefSp (V : HSp D) where
  s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ
  B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ
  L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  vol : Vol V

structure DefSp.Is {V : HSp D} (x : DefSp V) : Prop where
  sig : V.SigOK
  cpt : CoCpt V
  cart : ∀ τ, IsCartanInv (gramAt D V τ) (x.s τ)
  pm : ∀ τ, x.s τ = 1 ∨ x.s τ = -1
  onb : ∀ τ, ∃ p, IsONBasis (gramAt D V τ) (x.s τ) (x.B τ) p
  sd : IsSelfDualC V x.L

structure KerDat (S T : HSp D) where
  om : Om S T
  vac : WO S T → ℂ
  c : WO S T →₀ ℂ

structure KerDat.Is (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (x : DefSp S) (y : DefSp T) (k : KerDat S T) :
    Prop where
  weil : ∃ χS χT, IsWeilDatumO ψ S T χS χT k.om
  vac : IsVacO ψ θ S T x.s y.s x.L y.L k.vac
  fin : IsFinComb k.c

def KerDat.pt (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (x : DefSp S) (y : DefSp T) (k : KerDat S T)
    (P : PolF D T.rank S.rank) : WO S T → ℂ :=
  pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T k.c k.vac) P

def KerDat.lift (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (x : DefSp S) (y : DefSp T) (k : KerDat S T)
    (P : PolF D T.rank S.rank) (φ : GA D S → ℂ) : GA D T → ℂ :=
  liftT k.om x.vol.μ x.vol.𝓕 φ (k.pt ψ θ x y P)

def FockReduce (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'),
    x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z →
    ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → JointSmooth C →
      ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank),
        ∀ φ, IsContAut A φ → HasCen A χ φ →
          biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) =
            ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ)

def VanStep (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ) (φ : GA D B.A → ℂ) (G : GA D B'.V → ℂ) (g : GA D B.V)
    (t' : GA D J.W) (t'' : GA D B'.V) (J₁ : Set (GA D J.W)) (J₂ : Set (GA D B'.V)),
    IsThetaFunO ψ B.V J.W Φ₁ → IsThetaFunO ψ J.W B'.V Φ₂ → IsContAut B.A φ → RapidDec B'.V G →
    RapidDec J.W (s₂.lift G Φ₂) →
    (∀ k ∈ J₁, ∃ c : ℂ, c ≠ 0 ∧ s₁.om (1, k) Φ₁ = c⁻¹ • Φ₁ ∧ s₂.om (k, 1) Φ₂ = c • Φ₂) →
    (∀ k ∈ J₂, ∃ c : ℂ, c ≠ 0 ∧ s₂.om (1, k) Φ₂ = c⁻¹ • Φ₂ ∧ rTrans k G = c • G) →
    (∀ h₁, flatBF s₁ (s₁.om (g, h₁) Φ₁) ≠ 0 → InCell (jacGrp J.d) t' J₁ h₁) →
    (∀ a ∈ GinfC J.W, ∀ h₂, Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g (a * t') h₂ ≠ 0 → InCell (besGrp B'.d B'.o) t'' J₂ h₂) →
    (∀ a ∈ GinfC J.W, ∀ a' ∈ GinfC B'.V,
      B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g (a * t') (a' * t'')) (rTrans (a' * t'') G) = 0) →
    B.per ψ φ (rTrans g (s₁.lift (s₂.lift G Φ₂) Φ₁)) = 0

structure BesAt (V A : HSp D) (ρ : ℕ) where
  V₀ : HSp D
  L : HSp D
  d : HypDec V V₀ ρ
  o : OrthDec V₀ A L
  ζ : Fin L.rank → D.host.E
  line : IsLineVec L ζ
  cpt : CoCpt A
  vN : VolN d

@[reducible] def BesAt.lev {V A : HSp D} {ρ : ℕ} (b : BesAt V A ρ) (vA : Vol A) : BesLev D ρ :=
  ⟨V, b.V₀, A, b.L, b.d, b.o, b.ζ, b.line, b.cpt, vA, b.vN⟩

structure JacAt (W W₀ : HSp D) (ρ : ℕ) where
  d : HypDec W W₀ ρ
  cpt : CoCpt W₀
  vN : VolN d

@[reducible] def JacAt.lev {W W₀ : HSp D} {ρ : ℕ} (b : JacAt W W₀ ρ) (v0 : Vol W₀) : JacLev D ρ :=
  ⟨W, W₀, b.d, b.cpt, v0, b.vN⟩

open GlobalTheory.ChainOnto (Com PiLocalization₂ Reach)

structure StAt (V : HSp D) where
  par : D.what₂.Tau → SPar
  M : DSModel V par
  Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  β : GL (Fin V.rank) (Lev.EAf D)
  L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank
  ν : Measure (GA D V)
  fd : Set (GA D V)

@[reducible] def StAt.st {V : HSp D} (a : StAt V) : PiLocalization₂ D := ⟨V, a.par, a.M, a.Λ, a.β, a.L, a.ν, a.fd⟩

structure Geo (D : D7) where
  c : Com D
  bot : StAt (D.sp.Y 0)
  mid : ℕ → PiLocalization₂ D
  top : StAt D.sp.X'

def Geo.st (g : Geo D) : ℕ → PiLocalization₂ D
  | 0 => g.bot.st
  | j + 1 => g.mid j

abbrev Col (D : D7) (u : D.what₂.Word) (j : ℕ) : Type := (D.mem u).C.cls j → (D.mem u).C.Y j → ℂ

theorem idx_step {j σ m : ℕ} (h : j + 2 * (σ + 1) + 2 = m) : j + 1 + 1 + 2 * σ + 2 = m := by omega

set_option maxHeartbeats 1000000 in

structure Dat (D : D7) (u : D.what₂.Word) extends Geo D where

  p : ∀ j, GlobalTheory.ChainOnto.Step c (toGeo.st j) (toGeo.st (j + 1))
  pT : ∀ j, j + 2 * 0 + 2 = D.R.m → GlobalTheory.ChainOnto.Step c (toGeo.st (j + 1)) top.st

  t : ∀ j, GA D (toGeo.st j).V

  x : ∀ j, DefSp (D.sp.X j)
  k : ∀ j, KerDat (D.sp.X j) (D.sp.X (j + 1))

  bes : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (toGeo.st j).V (D.sp.X j) ρ
  jac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → JacAt (toGeo.st (j + 1)).V (D.sp.X (j + 1)) ρ
  sBF : ∀ j ρ h, StepBF c.ψ ((bes j ρ h).lev (x j).vol) ((jac j ρ h).lev (x (j + 1)).vol)
  sFB : ∀ j σ h, StepFB c.ψ ((jac j (σ + 1) h).lev (x (j + 1)).vol) ((bes (j + 1 + 1) σ (idx_step h)).lev (x (j + 1 + 1)).vol)
  lnk : ∀ j σ h, Link ((bes j (σ + 1) h).lev (x j).vol) (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ
  vL : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), VolM D (bes (j + 1 + 1) σ (idx_step h)).L.rank (D.sp.X (j + 1)).rank

  Lz : HSp D
  oT : ∀ n, n = D.R.m → OrthDec (D.sp.X n) D.sp.X' Lz

  Ram : ∀ j, Submodule ℂ (Col D u j)
  S : ∀ j, Col D u j →ₗ[ℂ] Col D u j
  rd : ∀ j, Col D u j → (D.mem u).C.Y j → GA D (D.sp.X j) → ℂ

  eT : (D.mem u).P.Mt → top.st.CC c

namespace Dat

variable {u : D.what₂.Word} (d : Dat D u)

abbrev B (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) : BesLev D ρ := (d.bes j ρ h).lev (d.x j).vol

abbrev lev (j : ℕ) : Set (GA D (d.st j).V) := levS (d.st j).V (d.st j).β (d.st j).L

def hand (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (P₁ : PolF D (d.st (j + 1)).V.rank (d.st j).V.rank)
    (P₂ : PolF D (d.st (j + 1 + 1)).V.rank (d.st (j + 1)).V.rank) (φ : GA D (D.sp.X j) → ℂ)
    (h₁ : GA D (d.st (j + 1)).V) (h₂ : GA D (d.st (j + 1 + 1)).V) : GA D (D.sp.X (j + 1 + 1)) → ℂ :=
  Chain.hand (d.sBF j (σ + 1) h) (d.sFB j σ h) (d.lnk j σ h) (d.vL j σ h) ((d.p j).pt P₁) ((d.p (j + 1)).pt P₂) φ (d.t j) h₁ h₂

def two (j : ℕ) (φ : GA D (D.sp.X j) → ℂ)
    (C : WO (D.sp.X j) (D.sp.X (j + 1)) → WO (D.sp.X (j + 1)) (D.sp.X (j + 1 + 1)) → ℂ) : GA D (D.sp.X (j + 1 + 1)) → ℂ :=
  biLift (d.k j).om (d.k (j + 1)).om (d.x j).vol (d.x (j + 1)).vol φ (biComb d.c.ψ _ _ _ (d.k j).c (d.k (j + 1)).c C)

def IsReal (j : ℕ) (C : WO (D.sp.X j) (D.sp.X (j + 1)) → WO (D.sp.X (j + 1)) (D.sp.X (j + 1 + 1)) → ℂ) : Prop :=
  IsBiVac d.c.ψ _ _ _ (d.x j).L (d.x (j + 1)).L (d.x (j + 1 + 1)).L C

def IsRealSm (j : ℕ) (C : WO (D.sp.X j) (D.sp.X (j + 1)) → WO (D.sp.X (j + 1)) (D.sp.X (j + 1 + 1)) → ℂ) : Prop :=
  d.IsReal j C ∧ JointSmooth C

structure Base : Prop where
  com : d.c.Is
  st : ∀ j, j < D.R.m → (d.st j).Is d.c j
  top : d.top.st.Is d.c D.R.m
  p : ∀ j, j + 1 < D.R.m → (d.p j).Is (j + 1)
  pT : ∀ j h, (d.pT j h).Is D.R.m
  t : ∀ j, d.t j ∈ GfC (d.st j).V
  x : ∀ j, j ≤ D.R.m → (d.x j).Is
  k : ∀ j, j < D.R.m → (d.k j).Is d.c.ψ d.c.θ (d.x j) (d.x (j + 1))
  sBF : ∀ j ρ h, (d.sBF j ρ h).om = (d.p j).ω ∧ (d.sBF j ρ h).vW.μ = (d.st (j + 1)).ν ∧ (d.sBF j ρ h).vW.𝓕 = (d.st (j + 1)).fd
  sFB : ∀ j σ h, (d.sFB j σ h).om = (d.p (j + 1)).ω ∧ (d.sFB j σ h).vW.μ = (d.st (j + 1 + 1)).ν ∧
    (d.sFB j σ h).vW.𝓕 = (d.st (j + 1 + 1)).fd

def Supp1 : Prop :=
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ h₁,
    flatBF (d.sBF j (σ + 1) h) ((d.p j).ω (d.t j, h₁) ((d.p j).pt P₁)) ≠ 0 →
      InCell (jacGrp (d.jac j (σ + 1) h).d) (d.t (j + 1)) (d.lev (j + 1)) h₁

def Supp2 : Prop :=
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂, ∀ ψ ∈ d.Ram j, ∀ y, ∀ a ∈ GinfC (d.st (j + 1)).V, ∀ h₂,
    d.hand j σ h P₁ P₂ (d.rd j ψ y) (a * d.t (j + 1)) h₂ ≠ 0 →
      InCell (besGrp (d.bes (j + 1 + 1) σ (idx_step h)).d (d.bes (j + 1 + 1) σ (idx_step h)).o) (d.t (j + 1 + 1))
        (d.lev (j + 1 + 1)) h₂

def Val : Prop :=
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂, ∀ a ∈ GinfC (d.st (j + 1)).V, ∀ a' ∈ GinfC (d.st (j + 1 + 1)).V,
    ∃ C, d.IsRealSm j C ∧ ∀ ψ ∈ d.Ram j, ∀ y,
      d.hand j σ h P₁ P₂ (d.rd j ψ y) (a * d.t (j + 1)) (a' * d.t (j + 1 + 1)) = d.two j (d.rd j (d.S j ψ) y) C

def ValLast : Prop :=
  ∀ j (h : j + 2 * 0 + 2 = D.R.m) P₁ P₂, ∃ C, d.IsRealSm j C ∧ ∀ ψ ∈ d.Ram j, ∀ y (F : d.top.st.CC d.c) (v : SmT d.top.M),
    (d.B j 0 h).per d.c.ψ (d.rd j ψ y) (rTrans (d.t j) (liftS (d.p j).ω (d.st (j + 1)).ν (d.st (j + 1)).fd
        (liftS (d.pT j h).ω d.top.ν d.top.fd (F.1 v) ((d.pT j h).pt P₂)) ((d.p j).pt P₁))) =
      ∫ h' in d.top.fd, F.1 v h' * d.two j (d.rd j (d.S j ψ) y) C ((d.oT (j + 1 + 1) h).emb (h', 1)) ∂d.top.ν

def KerLift : Prop :=
  ∀ j, j < D.R.m → ∀ y P, ∃ a : (D.mem u).C.Y (j + 1) →₀ ℂ, ∀ ψ ∈ d.Ram j,
    (d.k j).lift d.c.ψ d.c.θ (d.x j) (d.x (j + 1)) P (d.rd j ψ y) =
      ∑ y' ∈ a.support, a y' • d.rd (j + 1) ((D.mem u).C.K j ψ) y'

def PerLast : Prop :=
  ∀ y v, ∃ a : ℂ, ∀ ψ ∈ d.Ram D.R.m, ∀ F,
    ∫ h' in d.top.fd, (d.eT F).1 v h' * d.rd D.R.m ψ y ((d.oT D.R.m rfl).emb (h', 1)) ∂d.top.ν = a * (D.mem u).P.Ptil ψ F

def TopOnto : Prop := Function.Surjective d.eT

def RdLaw : Prop :=
  ∀ j, j ≤ D.R.m → ∃ χ, ∀ ψ ∈ d.Ram j, ∀ y, IsContAut (D.sp.X j) (d.rd j ψ y) ∧ HasCen (D.sp.X j) χ (d.rd j ψ y)

def Stab : Prop :=
  (∀ j, j < D.R.m → ∀ ψ ∈ d.Ram j, (D.mem u).C.K j ψ ∈ d.Ram (j + 1)) ∧ (∀ j, j ≤ D.R.m → ∀ ψ ∈ d.Ram j, d.S j ψ ∈ d.Ram j) ∧
    (D.mem u).A.Mram ≤ d.Ram 0

def Comm : Prop :=
  (∀ j, j < D.R.m → ∃ c : ℂ, ∀ ψ ∈ d.Ram j, d.S (j + 1) ((D.mem u).C.K j ψ) = c • (D.mem u).C.K j (d.S j ψ)) ∧
    (∀ ψ ∈ (D.mem u).A.Mram, d.S 0 ψ ∈ (D.mem u).A.Mram) ∧ ∀ ψ ∈ (D.mem u).A.Mram, d.S 0 ψ = 0 → ψ = 0

def VanAt (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) (ψ : Col D u j) (G : (d.st j).CC d.c) : Prop :=
  ∀ y (v : SmT (d.st j).M), (d.B j ρ h).per d.c.ψ (d.rd j ψ y) (rTrans (d.t j) (G.1 v)) = 0

def Bot : Prop :=
  ∃ V : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u, Function.Injective V ∧ ∀ φ : (D.mem u).A.Mram,
    (∀ ρ h G, d.VanAt 0 ρ h φ.1 G) → D.s.Pu u (V φ) = 0

def StepVan : Prop :=
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∀ ψ ∈ d.Ram j, ∀ G : (d.st (j + 1 + 1)).CC d.c,
    d.VanAt (j + 1 + 1) σ (idx_step h) ((D.mem u).C.K (j + 1) ((D.mem u).C.K j (d.S j ψ))) G →
      d.VanAt j (σ + 1) h ψ ((d.p j).io ((d.p (j + 1)).io G))

def LastVan : Prop :=
  ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∀ ψ ∈ d.Ram j, ∀ F : (D.mem u).P.Mt,
    (D.mem u).P.Ptil (Eq.rec (motive := fun n _ => Col D u n)
        ((D.mem u).C.K (j + 1) ((D.mem u).C.K j (d.S j ψ))) (show j + 1 + 1 = D.R.m from h)) F = 0 →
      d.VanAt j 0 h ψ ((d.p j).io ((d.pT j h).io (d.eT F)))

end Dat

example {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {f : WO A S → ℂ} {g : WO S A' → ℂ}
    (hf : IsThetaFunO ψ A S f) (hg : IsThetaFunO ψ S A' g) : JointSmooth fun u v => f u * g v :=
  fun n L L' c c' h h' u v => (hf.smooth n L c h u).mul (hg.smooth n L' c' h' v)

example {V : HSp D} (R : Subgroup (GA D V)) (t : GA D V) : InCell R t {1} t := ⟨1, one_mem _, 1, one_mem _, 1, rfl, by simp⟩

example (A : HSp D) : HasCen A (fun _ => 1) (fun _ => 1) ∧ ¬ HasCen A (fun _ => 2) (fun _ => 1) :=
  ⟨fun _ _ _ _ => by simp, fun h => by simpa using h 1 (one_mem _) (one_mem _) 1⟩

end GlobalTheory.SeeSaw

end
