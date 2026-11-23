import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

abbrev Mt (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

section Local

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def frDom (Hm : Mt n) (q : ℕ) : Set (Mt n) :=
  {x | x.det ≠ 0 ∧ ∀ i : Fin (n + 1),
    0 < ReciprocityTheory.ChartRestriction.G.FD.psgn q i * (ReciprocityTheory.ChartRestriction.G.FD.lminor (-(xᴴ * Hm * x)) i).re}

def UpT (b : Mt n) : Prop := b.det ≠ 0 ∧ ∀ a c : Fin n, c < a → b a c = 0

def OrthFr (Hm : Mt n) (q : ℕ) (x₀ : Mt n) : Prop :=
  q ≤ n ∧ x₀ᴴ * Hm * x₀ = diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)

def UG (Hm : ι → Mt n) : Set (ι → Mt n) := {u | ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (Hm τ)}

def frDoms (Hm : ι → Mt n) (q : ι → ℕ) : Set (ι → Fin n → Fin n → ℂ) := {x | ∀ τ, Matrix.of (x τ) ∈ frDom (Hm τ) (q τ)}

def HolSec (Hm : ι → Mt n) (q : ι → ℕ) (w : ι → Fin n → ℤ) (P : (ι → Fin n → Fin n → ℂ) → ℂ) : Prop :=
  DifferentiableOn ℂ P (frDoms Hm q) ∧
    ∀ x ∈ frDoms Hm q, ∀ b : ι → Mt n, (∀ τ, UpT (b τ)) →
      P (fun τ => (Matrix.of (x τ) * b τ : Mt n)) = (∏ τ, ∏ a, b τ a a ^ w τ a) * P x

def HolFn (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ) (f : (ι → Mt n) → ℂ) : Prop :=
  ∃ P, HolSec Hm q w P ∧ ∀ u ∈ UG Hm, f u = P fun τ => (u τ * x₀ τ : Mt n)

def lieH (Hm : Mt n) : Set (Mt n) := {X | Xᴴ * Hm + Hm * X = 0}

def SmFn (Hm : ι → Mt n) (f : (ι → Mt n) → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → ι) (Xs : Fin k → Mt n), (∀ i, Xs i ∈ lieH (Hm (τs i))) → ∀ u ∈ UG Hm,
    ContDiff ℝ ∞ fun t : Fin k → ℝ =>
      f (u * (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod)

def der (τ : ι) (X : Mt n) (f : (ι → Mt n) → ℂ) (u : ι → Mt n) : ℂ :=
  deriv (fun t : ℝ => f (u * (Pi.mulSingle τ (NormedSpace.exp (t • X)) : ι → Mt n))) 0

def conjH (Hm Z : Mt n) : Mt n := -(Hm⁻¹ * Zᴴ * Hm)

def derC (Hm : ι → Mt n) (τ : ι) (Z : Mt n) (f : (ι → Mt n) → ℂ) (u : ι → Mt n) : ℂ :=
  der τ ((1 / 2 : ℂ) • (Z + conjH (Hm τ) Z)) f u + Complex.I * der τ ((1 / (2 * Complex.I)) • (Z - conjH (Hm τ) Z)) f u

def KilledFn (Hm : ι → Mt n) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ) (f : (ι → Mt n) → ℂ) : Prop :=
  ∀ τ (a c : Fin n), a ≤ c → ∀ u ∈ UG Hm,
    derC Hm τ (x₀ τ * Matrix.single a c 1 * (x₀ τ)⁻¹) f u = if a = c then (w τ a : ℂ) * f u else 0

def torEl (x₀ : ι → Mt n) (s : ι → Fin n → ℝ) : ι → Mt n :=
  fun τ => x₀ τ * diagonal (fun a => Complex.exp ((s τ a : ℂ) * Complex.I)) * (x₀ τ)⁻¹

def torCh (w : ι → Fin n → ℤ) (s : ι → Fin n → ℝ) : ℂ := ∏ τ, ∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a

def dRepC {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Hm : Mt n) (σ : Mt n → (H →L[ℂ] H)) (Z : Mt n) (v : H) : H :=
  dRep σ ((1 / 2 : ℂ) • (Z + conjH Hm Z)) v + Complex.I • dRep σ ((1 / (2 * Complex.I)) • (Z - conjH Hm Z)) v

def gelfRep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Hm : Mt n) (σ : Mt n → (H →L[ℂ] H)) (k : ℕ) (v : H) : H :=
  ∑ idx : Fin (k + 1) → Fin n,
    (List.ofFn fun a : Fin (k + 1) => dRepC Hm σ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr (fun f acc => f acc) v

def InZe (Hm : Mt n) (e : Fin n → ℂ) (m : Mt n) : Prop :=
  ∃ s : ℝ, m = 1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm)

end Local

section Adelic

variable {D : D7}

def HolShape {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Prop :=
  ∀ τ, Formalism.QuantumDeterminants.IsHCParam (M.lam τ) ∧ ∃ p ≤ V.rank, ∀ a, M.ε τ a = decide ((a : ℕ) < p)

def WtIs {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) : Prop :=
  ∀ τ c, (w τ c : ℝ) = extWt M τ (arr (nNeg (M.ε τ)) c)

open Classical in

def HolAd (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ)
    (φ : GA D V → ℂ) : Prop :=
  ∀ g, ∃ f, HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w f ∧
    ∀ u ∈ GinfC V, φ (g * u) = f fun τ => archM V (θ τ) u

def ZI (V : HSp D) (ξ : Fin V.rank → D.host.E) : Subgroup (GA D V) :=
  Subgroup.closure {g | ∃ a : AF D.host.F ⊗[D.host.F] D.host.E,
    ((matHom V g).1 - 1 : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) =
      a • (vecMulVec ξ ((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ᵥ* V.gram)).map (incA D)}

def IsoVec (V : HSp D) (ξ : Fin V.rank → D.host.E) : Prop :=
  ξ ≠ 0 ∧ (fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ⬝ᵥ V.gram.mulVec ξ = 0

def ZCusp (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ ξ, IsoVec V ξ → ∀ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure →
    IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ → ∀ g, ∫ z in 𝓕, φ ((z : GA D V) * g) ∂μ = 0

structure HolForm (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (φ : GA D V → ℂ) : Prop where
  aut : IsAutFun V φ
  bdd : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C
  lev : ∀ k ∈ J, ∀ g, φ (g * k) = χ k * φ g
  hol : HolAd θ M w φ

structure FinPair (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop where
  haar : μ.IsHaarMeasure
  right : μ.IsMulRightInvariant
  fd : IsFundamentalDomain (GQ V) 𝓕 μ
  fin : μ 𝓕 ≠ ⊤

def nuQ (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Measure (AutQ V) := (μ.restrict 𝓕).map (autMk V)

def Repr (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (F : Lp ℂ 2 (nuQ V μ 𝓕)) (ψ : GA D V → ℂ) : Prop :=
  ∀ᵐ x ∂μ, F (autMk V x) = ψ x

structure IsReg (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))) : Prop where
  val : ∀ g F, ∀ᵐ x ∂μ, ρ g F (autMk V x) = F (autMk V (x * g))
  iso : ∀ g F, ‖ρ g F‖ = ‖F‖
  cont : ∀ F, Continuous fun g => ρ g F

def IsSmoothVector' (θ : InfFam D) (V : HSp D) {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (F : K) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Mt V.rank), (∀ i, Xs i ∈ lieAt V (τs i)) →
    ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod F

def dL2 (θ : InfFam D) (V : HSp D) {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (p : D.what₂.Tau × Mt V.rank) (F : K) : K :=
  deriv (fun t : ℝ => ρ (oneP θ V p.1 p.2 t) F) 0

structure GoodDict (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ)
    {r : ℕ} (hr : V.rank = r) {Comp : Type} (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r)
    (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) (Kf : Subgroup (GA D V)) : Prop where
  inf : IsInfFam θ
  base : BaseFr M θ hr dict
  unif : ∃ th, (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr
  model : ∀ k, ModelW V hr (X k)
  muUnit : MuUnit V dict mu
  muCont : Continuous mu
  chi : ∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1
  cNe : ∀ k, c k ≠ 0
  cBdd : ∃ C : ℝ, ∀ k, ‖c k‖ ≤ C
  fin : Finite Comp
  levFin : Kf ≤ GfC V
  levOpen : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ Kf
  muK : ∀ k ∈ Kf, mu k = 1
  wt : ∃ e : D.what₂.Tau → ℤ, (∀ u ∈ GinfC V, mu u = ∏ ρ, (archM V (θ ρ) u).det ^ e ρ) ∧
    ∀ k ρ (τ : (X k).Ψ), τ.1 = tauE D ρ → ∀ a : Fin V.rank, w ρ a = la k τ (Fin.cast hr a) + e ρ

end Adelic

end GlobalTheory.HolDict
