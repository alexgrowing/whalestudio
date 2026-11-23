import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace Formalism.MainNotions.TaylorLogMetric

open NumberField Formalism.BasicNotions Classical
open scoped Pointwise

def chK (D : D7) : DirichletCharacter ℂ D.host.d :=
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  (quadraticChar (ZMod D.host.d)).ringHomComp (Int.castRingHom ℂ)

def logDerivativeAtOne (D : D7) : ℝ :=
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  (deriv (DirichletCharacter.LFunction (chK D)) 1 / DirichletCharacter.LFunction (chK D) 1).re

def logOmVal (D : D7) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.pi / D.host.v) - logDerivativeAtOne D

def fF (D : D7) : ℕ := D.R.f

def embT (D : D7) (τ : D.what₂.Tau) : D.host.E →+* ℂ := D.host.emb (D.eTau τ : D.R.GG)

def homL (D : D7) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) :=
  Submodule.span (𝓞 D.host.E) {A | ∀ x ∈ L, A.mulVec x ∈ L'}

def YYl (D : D7) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) :=
  Submodule.span (𝓞 D.host.E)
    {B | ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ A ∈ homL D L L', B = a • A}

def hYY (D : D7) {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) : D.host.K :=
  Algebra.trace D.host.K D.host.E (∑ i, ∑ j, x i j * D.host.conj (y i j))

def eisG (Λ : AddSubgroup ℂ) (k : ℕ) : ℂ :=
  ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)

def g2 (Λ : AddSubgroup ℂ) : ℂ := 60 * eisG Λ 2

def g3 (Λ : AddSubgroup ℂ) : ℂ := 140 * eisG Λ 3

def discr (Λ : AddSubgroup ℂ) : ℂ := g2 Λ ^ 3 - 27 * g3 Λ ^ 2

def area (Λ : AddSubgroup ℂ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, a = |((starRingEnd ℂ) w₁ * w₂).im|}

def lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : AddSubgroup ℂ :=
  AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * D.host.φ₀ (((c : D.host.K) : D.host.E))}

def IsCurveIdeal (D : D7) (cc : Ideal (𝓞 D.host.K)) : Prop :=
  cc ≠ ⊥ ∧ Nat.Coprime (Ideal.absNorm cc) (2 * D.host.d)

def IsDiscriminantTwelfthRootOfIdealLattice (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop :=
  δ ^ 12 = discr (lamOf D cc 1)

structure Tor (D : D7) where
  emb : D.what₂.Tau → D.host.E → ℂ
  abelian₂ : AddSubgroup ℂ

abbrev VC (D : D7) (N N' : ℕ) : Type := D.what₂.Tau → Fin N' → Fin N → ℂ

def tor0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Tor D :=
  ⟨fun τ => embT D τ, lamOf D cc δ⟩

def embV (D : D7) (T : Tor D) {N N' : ℕ} (A : Matrix (Fin N') (Fin N) D.host.E) : VC D N N' :=
  fun τ i j => T.emb τ (A i j)

def La (D : D7) (T : Tor D) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : AddSubgroup (VC D N N') :=
  AddSubgroup.closure {z | ∃ w ∈ T.abelian₂, ∃ A ∈ YYl D L L', z = w • embV D T A}

def Hf (D : D7) (T : Tor D) {N N' : ℕ} (z w : VC D N N') : ℂ :=
  (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (area T.abelian₂ : ℂ)

def al (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : ℂ :=
  (-1 : ℂ) ^ (round (Real.sqrt D.host.d / 2 * (Hf D T x x).re))

def U (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (G : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2)

def ThSp (D : D7) (T : Tor D) {N N' : ℕ} (La' : AddSubgroup (VC D N N')) : Set (VC D N N' → ℂ) :=
  {G | Differentiable ℂ G ∧ ∀ x ∈ La', ∀ z, al D T x * U D T x G z = G z}

def Th (D : D7) (T : Tor D) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Set (VC D N N' → ℂ) :=
  ThSp D T (La D T L L')

def normSq (D : D7) (T : Tor D) {N N' : ℕ} (La' : AddSubgroup (VC D N N'))
    (G : VC D N N' → ℂ) : ℝ :=
  let Fd : Set (VC D N N') :=
    Classical.epsilon (fun Fd => MeasureTheory.IsAddFundamentalDomain La' Fd MeasureTheory.volume)
  ⨍ z in Fd, ‖G z‖ ^ 2 * Real.exp (-Real.pi * (Hf D T z z).re)

def Iop (D : D7) (T : Tor D) {N N' : ℕ} (La₁ La₂ : AddSubgroup (VC D N N'))
    (G : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
    ∑ᶠ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      al D T ((Quotient.out q : La₂) : VC D N N') * U D T ((Quotient.out q : La₂) : VC D N N') G z

def pull (D : D7) (T : Tor D) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (G : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => G (fun τ => (Matrix.conjTranspose (γ'.map (T.emb τ)) * (Matrix.of (z τ)) * γ.map (T.emb τ) : Matrix _ _ ℂ))

abbrev Mono (D : D7) (N N' : ℕ) : Type := (D.what₂.Tau × Fin N' × Fin N) →₀ ℕ

def coordV (D : D7) {N N' : ℕ} (k : D.what₂.Tau × Fin N' × Fin N) : VC D N N' :=
  fun τ i j => if τ = k.1 ∧ i = k.2.1 ∧ j = k.2.2 then 1 else 0

def taylor (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) (α : Mono D N N') : ℂ :=
  iteratedFDeriv ℂ (Multiset.card α.toMultiset) G 0
      (fun i => coordV D (α.toMultiset.toList.get ⟨i, by simpa using i.2⟩)) /
    (α.prod fun _ n => (n.factorial : ℂ))

def mono (D : D7) {N N' : ℕ} (α : Mono D N N') (z : VC D N N') : ℂ :=
  α.prod fun k n => z k.1 k.2.1 k.2.2 ^ n

def liftM (M : IntermediateField ℚ ℂ) (x : ℂ) : M := if h : x ∈ M then ⟨x, h⟩ else 0

def lamConj (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (Λ : AddSubgroup ℂ) : AddSubgroup ℂ :=
  Classical.epsilon (fun Λ' : AddSubgroup ℂ =>
    g2 Λ' = ρ (liftM M (g2 Λ)) ∧ g3 Λ' = ρ (liftM M (g3 Λ)))

def torConj (D : D7) (T : Tor D) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : Tor D :=
  ⟨fun τ x => ρ (liftM M (T.emb τ x)), lamConj M ρ T.abelian₂⟩

def fnConj (D : D7) {N N' : ℕ} (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (G : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => ∑' α : Mono D N N', ρ (liftM M (taylor D G α)) * mono D α z

def DataIn (D : D7) (T : Tor D) (M : IntermediateField ℚ ℂ) : Prop :=
  (∀ τ x, T.emb τ x ∈ M) ∧ g2 T.abelian₂ ∈ M ∧ g3 T.abelian₂ ∈ M

def CoefIn (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) (M : IntermediateField ℚ ℂ) : Prop :=
  ∀ α, taylor D G α ∈ M

def meanLogNormSq (D : D7) (T : Tor D) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (G : VC D N N' → ℂ) : ℝ :=
  (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (normSq D (torConj D T M ρ) (La D (torConj D T M ρ) L L')
      (fnConj D M ρ G))) / (Module.finrank ℚ M : ℝ)

def mmM (D : D7) (M : IntermediateField ℚ ℂ) [NumberField M] :
    Submodule (𝓞 M) (D.what₂.Tau → M) :=
  Submodule.span (𝓞 M) {v | ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
    v = fun τ => liftM M (embT D τ a)}

def ellT (D : D7) (M : IntermediateField ℚ ℂ) [NumberField M] (τ : D.what₂.Tau) :
    Submodule (𝓞 M) M :=
  (mmM D M).comap (LinearMap.single (𝓞 M) (fun _ : D.what₂.Tau => (M : Type)) τ)

def logMet (M : IntermediateField ℚ ℂ) (Λ : AddSubgroup ℂ) (ρ : M →ₐ[ℚ] ℂ) (s : M) : ℝ :=
  Real.log (Real.pi * ‖ρ s‖ ^ 2 / area (lamConj M ρ Λ))

def meanLogOm (D : D7) (Λ : AddSubgroup ℂ) (M : IntermediateField ℚ ℂ) [NumberField M]
    (τ : D.what₂.Tau) : ℝ :=
  let s : M := Classical.epsilon (fun s : M => s ≠ 0 ∧ s ∈ ellT D M τ)
  (2 * Real.log ((((Submodule.span (𝓞 M) {s}).toAddSubgroup.addSubgroupOf
      (ellT D M τ).toAddSubgroup).index : ℕ) : ℝ) -
    ∑ ρ : M →ₐ[ℚ] ℂ, logMet M Λ ρ s) / (Module.finrank ℚ M : ℝ)

abbrev FamE (D : D7) : Type :=
  ∀ (N N' : ℕ), Submodule (𝓞 D.host.E) (Fin N → D.host.E) →
    Submodule (𝓞 D.host.E) (Fin N' → D.host.E) → VC D N N' → ℂ

def admitted (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Prop :=
  letI := D.host.cmStar
  Even N ∧ Even N' ∧ IsSDLat D.host.E N L ∧ IsSDLat D.host.E N' L'

abbrev Qbar : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

def lamC {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : ℂ) : ℂ_[p] :=
  if h : x ∈ Qbar then lam ⟨x, h⟩ else 0

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def wModel {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ) :
    WeierstrassCurve ℂ_[p] :=
  ⟨0, 0, 0, lamC lam (-(g2 Λ) / 4), lamC lam (-(g3 Λ) / 4)⟩

def IsModel {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) : Prop :=
  let W := C • wModel lam Λ
  IsIntP W.a₁ ∧ IsIntP W.a₂ ∧ IsIntP W.a₃ ∧ IsIntP W.a₄ ∧ IsIntP W.a₆ ∧ W.Δ = 1

def dX {A : Type*} [CommRing A] (f : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => ((n : A) + 1) * PowerSeries.coeff (n + 1) f

def IsWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Prop :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  wq = 1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3

def omegaW {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  (-(2 : PowerSeries ℂ_[p]) * wq - X * dX wq) * (wq * (c W.a₁ * X + c W.a₃ * X ^ 3 * wq - 2))⁻¹

def flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) (omegaW W wq) / n

def pSer (D : D7) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (G : VC D N N' → ℂ) :
    MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] :=
  fun α => lamC lam (taylor D G α)

def LocBasis (D : D7) {N N' r : ℕ} (p : ℕ) (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E))
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) : Prop :=
  LinearIndependent D.host.K b ∧
  (∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) • b i ∈ Y) ∧
  ∀ y ∈ Y, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : Fin r → 𝓞 D.host.K,
    (s : D.host.E) • y = ∑ i, (((c i : D.host.K) : D.host.E)) • b i

def Orthonormal (D : D7) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) : Prop :=
  ∀ i j, hYY D (b i) (b j) = if i = j then 1 else 0

def atLog (D : D7) {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    MvPowerSeries (Fin r) ℂ_[p] :=
  let W := C • wModel lam Λ
  MvPowerSeries.subst (fun k : D.what₂.Tau × Fin N' × Fin N => ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p])
      (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
      PowerSeries.subst (MvPowerSeries.X i) (flog W wq)) F

def U1 (Λ : AddSubgroup ℂ) (ω : ℂ) (G : ℂ → ℂ) : ℂ → ℂ :=
  fun z => G (z + ω) * Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) -
    (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ)))

def sgStar (Λ : AddSubgroup ℂ) : ℂ → ℂ :=
  Classical.epsilon (fun G : ℂ → ℂ => Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
    ∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z)

def sgSer {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ) : PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => lamC lam (iteratedDeriv n (sgStar Λ) 0 / (n.factorial : ℂ))

def ePhi1 {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  let ep : ℂ_[p] := ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])
  PowerSeries.mk fun n => ep⁻¹ * PowerSeries.coeff (n + 1)
    (PowerSeries.subst (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) ep * flog (C • wModel lam Λ) wq)
      (sgSer lam Λ))

def ePh {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (r : ℕ) :
    MvPowerSeries (Fin r) ℂ_[p] :=
  if p = 2 then 1 else
    ∏ i : Fin r, (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p])
      (ePhi1 lam Λ C wq))⁻¹

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

def pd {σ : Type*} [DecidableEq σ] {A : Type*} [CommRing A] (k : σ) (F : MvPowerSeries σ A) :
    MvPowerSeries σ A :=
  fun n => ((n k : A) + 1) * MvPowerSeries.coeff (n + Finsupp.single k 1) F

def der (D : D7) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (y : Matrix (Fin N') (Fin N) D.host.E)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] :=
  ∑ k : D.what₂.Tau × Fin N' × Fin N,
    algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (lamC lam (embT D k.1 (y k.2.1 k.2.2))) *
      pd k F

def JetsInt (D : D7) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E))
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : Prop :=
  ∀ (n : ℕ) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ i, y i ∈ Y) →
    IsIntP (MvPowerSeries.constantCoeff ((List.ofFn y).foldr (fun y' G => der D lam y' G) F))

def TorsPrime (D : D7) {N N' : ℕ} (p : ℕ) (La' : AddSubgroup (VC D N N')) (t : VC D N N') : Prop :=
  ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ n • t ∈ La'

def EqAt {N : ℕ} (D : D7) (p : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ L, (s : D.host.E) • x ∈ L₁) ∧ ∀ x ∈ L₁, (s : D.host.E) • x ∈ L

def IsComb (D : D7) (T : Tor D) (e : FamE D) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : Prop :=
  ∃ (m : ℕ) (r : Fin m → ℂ_[p]) (t : Fin m → VC D N N')
    (L₁ : Fin m → Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₁' : Fin m → Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    (∀ k, IsIntP (r k)) ∧ (∀ k, TorsPrime D p (La D T L L') (t k)) ∧
    (∀ k, admitted D N N' (L₁ k) (L₁' k) ∧ EqAt D p L (L₁ k) ∧ EqAt D p L' (L₁' k)) ∧
    F = ∑ k, algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (r k) *
      pSer D lam (U D T (t k) (e N N' (L₁ k) (L₁' k)))

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def sgm (D : D7) : D.R.GG := ((-1, 1), 1)

def tauSg (D : D7) (τ : D.what₂.Tau) : D.what₂.Tau :=
  if h : (D.eTau τ : D.R.GG) * sgm D ∈ D.R.Psi then D.eTau.symm ⟨_, h⟩ else τ

def Qd (D : D7) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (u : D.what₂.Tau → ℂ_[p]) :
    MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] :=
  ∑ τ : D.what₂.Tau, ∑ a : Fin N', ∑ b : Fin N,
    algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (u τ) *
      MvPowerSeries.X (τ, a, b) * MvPowerSeries.X (tauSg D τ, a, b)

abbrev IdE (D : D7) : Type := Submodule (𝓞 D.host.E) D.host.E

def N1 (D : D7) (𝔞 : IdE D) : Prop :=
  ∃ 𝔟 : IdE D, (∀ x, x ∈ 𝔟 ↔ D.host.conj x ∈ 𝔞) ∧ 𝔞 * 𝔟 = 1

def detId (D : D7) {N : ℕ} (L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : IdE D :=
  Submodule.span (𝓞 D.host.E)
    {x | ∃ A : Matrix (Fin N) (Fin N) D.host.E, (∀ v ∈ L, A.mulVec v ∈ L') ∧ x = A.det}

def IsChi (D : D7) (χ : IdE D → ℂ) : Prop :=
  (∀ 𝔞 𝔟, N1 D 𝔞 → N1 D 𝔟 → χ (𝔞 * 𝔟) = χ 𝔞 * χ 𝔟) ∧
  letI := D.host.cmStar
  ∀ z : unitary D.host.E,
    χ (Submodule.span (𝓞 D.host.E) {(z : D.host.E)}) = ∏ τ : D.what₂.Tau, (embT D τ (z : D.host.E))⁻¹

def qH (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : ℝ :=
  Real.sqrt D.host.d / 2 * (Hf D T x x).re

def wPh (D : D7) (T : Tor D) {N N' : ℕ} (p : ℕ) (x : VC D N N') : ℂ :=
  if p = 2 then Complex.exp ((Real.pi : ℂ) * Complex.I * (qH D T x : ℂ))
  else Classical.epsilon (fun s : ℂ =>
    ∃ (k : ℕ) (m : ℤ), (p : ℝ) ^ k * qH D T x = (m : ℝ) ∧ s = (-1 : ℂ) ^ m)

def Wop (D : D7) (T : Tor D) {N N' : ℕ} (p : ℕ) (x : VC D N N') (G : VC D N N' → ℂ) :
    VC D N N' → ℂ :=
  fun z => wPh D T p x * U D T x G z

def kap (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((Hf D T x y).im : ℂ))

def NNBasis (D : D7) (T : Tor D) (δ : ℂ) (p : ℕ) {N N' r : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) : Prop :=
  LocBasis D p (YYl D L L') b ∧ ∀ i, δ • embV D T (b i) ∈ La D T L L'

def IsIdem (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (m : ℕ) (ε : 𝓞 D.host.K) : Prop :=
  ‖lamC lam (D.host.φ₀ ((ε : D.host.K) : D.host.E)) - 1‖ ≤ (p : ℝ) ^ (-(m : ℤ)) ∧
  ‖lamC lam (D.host.φ₀ (D.host.conj ((ε : D.host.K) : D.host.E)))‖ ≤ (p : ℝ) ^ (-(m : ℤ))

def liftY (D : D7) (T : Tor D) (δ : ℂ) {N N' r : ℕ} (p n : ℕ) (ε : 𝓞 D.host.K)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Fin r → Fin (p ^ n)) : VC D N N' :=
  δ • embV D T ((((ε : D.host.K) : D.host.E) / (p : D.host.E) ^ n) •
    ∑ i, (((y i : ℕ) : D.host.E)) • b i)

def vecN (D : D7) (T : Tor D) (δ : ℂ) {N N' r : ℕ} (p n : ℕ)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (a : Fin r → Fin (p ^ n)) : VC D N N' :=
  δ • embV D T (∑ i, (((a i : ℕ) : D.host.E)) • b i)

def FactorsMod {p r : ℕ} [Fact p.Prime] (n : ℕ) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ) : Prop :=
  ∀ a a' : Fin r → ℤ_[p], (∀ i, ‖a i - a' i‖ ≤ (p : ℝ) ^ (-(n : ℤ))) → Φ a = Φ a'

def XiF (D : D7) (T : Tor D) (δ : ℂ) {N N' r : ℕ} (p n : ℕ) [Fact p.Prime] (ε : 𝓞 D.host.K)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ)
    (G : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => ((p : ℂ) ^ (n * r))⁻¹ * ∑ a : Fin r → Fin (p ^ n), Φ (fun i => (((a i : ℕ) : ℤ_[p]))) *
    ∑ y : Fin r → Fin (p ^ n), (kap D T (vecN D T δ p n b a) (liftY D T δ p n ε b y))⁻¹ *
      Wop D T p (liftY D T δ p n ε b y) G z

def expPS {p : ℕ} [Fact p.Prime] (F : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff n (F ^ k) / (k.factorial : ℂ_[p])

def IsOmP {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ) (Ω : ℂ_[p]) : Prop :=
  ‖Ω‖ = 1 ∧ ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    IsModel lam Λ C → IsWq (C • wModel lam Λ) wq →
    ∀ n, IsIntP (PowerSeries.coeff n (expPS (algebraMap ℂ_[p] (PowerSeries ℂ_[p])
      (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) / Ω) * flog (C • wModel lam Λ) wq)))

def zc {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) : ℂ_[p] := algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])

def pairN (D : D7) {N N' r p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Matrix (Fin N') (Fin N) D.host.E)
    (a : Fin r → ℤ_[p]) : ℂ_[p] :=
  Ω⁻¹ * ∑ i, zc (a i) * lamC lam (D.host.φ₀ ((hYY D y (b i) : D.host.K) : D.host.E))

def jet (D : D7) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {n : ℕ}
    (y : Fin n → Matrix (Fin N') (Fin N) D.host.E)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : ℂ_[p] :=
  MvPowerSeries.constantCoeff ((List.ofFn y).foldr (fun y' G => der D lam y' G) F)

def EqAway {N : ℕ} (D : D7) (p : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  ∃ k : ℕ, (∀ x ∈ L, ((p : D.host.E) ^ k) • x ∈ L₁) ∧ ∀ x ∈ L₁, ((p : D.host.E) ^ k) • x ∈ L

def NonzeroIndexPlace {l : ℕ} [Fact l.Prime] (c : ℂ_[l]) : Prop :=
  c ∈ closure {x : ℂ_[l] | ∃ m : ℕ, 0 < m ∧ Nat.Coprime m l ∧ ∃ (ζ : ℂ_[l]) (a : Fin m → ℚ_[l]),
    ζ ^ m = 1 ∧ x = ∑ k, algebraMap ℚ_[l] ℂ_[l] (a k) * ζ ^ (k : ℕ)}

def InW {l : ℕ} [Fact l.Prime] (c : ℂ_[l]) : Prop := NonzeroIndexPlace c ∧ ‖c‖ ≤ 1

def posG (D : D7) (φ : D.R.GG) {d : ℕ} (τ0 : D.what₂.Tau) (s : ZMod d) :
    D.R.GG :=
  (D.eTau τ0 : D.R.GG) * φ ^ s.val

def letterOf (D : D7) (φ : D.R.GG) {d : ℕ} (τ0 : D.what₂.Tau) (s : ZMod d) : D.what₂.Tau :=
  if h : posG D φ τ0 s ∈ D.R.Psi then D.eTau.symm ⟨_, h⟩
  else if h' : D.R.cc * posG D φ τ0 s ∈ D.R.Psi then D.eTau.symm ⟨_, h'⟩
  else τ0

structure Pos (D : D7) (p d : ℕ) where
  φ : D.R.GG
  frob : ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})],
    IsArithFrobAt ℤ (D.host.sigmaOf φ) P
  d_eq : d = orderOf φ
  V : Finset D.what₂.Tau
  bij : Function.Bijective (fun x : {v // v ∈ V} × ZMod d => letterOf D φ x.1.1 x.2)

def posEmb (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (φ : D.R.GG) {d : ℕ}
    (τ0 : D.what₂.Tau) (s : ZMod d) : D.host.E → ℂ_[p] :=
  fun x => lamC lam (D.host.emb (posG D φ τ0 s) x)

def LocBasisW (D : D7) {p : ℕ} [Fact p.Prime] (ρ : D.host.E → ℂ_[p]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (P : Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  P.det ≠ 0 ∧ (∀ a, ∃ s : 𝓞 D.host.E, ‖ρ (s : D.host.E)‖ = 1 ∧ s • P.transpose a ∈ L) ∧
  ∀ x ∈ L, ∃ s : 𝓞 D.host.E, ‖ρ (s : D.host.E)‖ = 1 ∧ ∃ c : Fin N → 𝓞 D.host.E,
    s • x = ∑ a, c a • P.transpose a

abbrev TVar (D : D7) {p d : ℕ} (Po : Pos D p d) (N N' : ℕ) : Type :=
  ZMod d × ({v // v ∈ Po.V} × Fin N × Fin N')

def chg (D : D7) {p d : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Po : Pos D p d) {N N' : ℕ}
    (P : {v // v ∈ Po.V} → Matrix (Fin N) (Fin N) D.host.E)
    (P' : {v // v ∈ Po.V} → Matrix (Fin N') (Fin N') D.host.E)
    (k : D.what₂.Tau × Fin N' × Fin N) (j : TVar D Po N N') : ℂ_[p] :=
  let ρ := posEmb D lam Po.φ j.2.1.1 j.1
  if letterOf D Po.φ j.2.1.1 j.1 = k.1 then
    (if posG D Po.φ j.2.1.1 j.1 ∈ D.R.Psi then
      ((P' j.2.1).map ρ) k.2.1 j.2.2.2 * (((P j.2.1).map ρ)⁻¹) j.2.2.1 k.2.2
    else
      ((((P' j.2.1).map ρ)⁻¹).transpose) k.2.1 j.2.2.2 * (((P j.2.1).map ρ).transpose) j.2.2.1 k.2.2)
  else 0

def atLin {σ κ : Type*} [Fintype κ] {p : ℕ} [Fact p.Prime] (c : σ → κ → ℂ_[p])
    (w : κ → MvPowerSeries κ ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries κ ℂ_[p] :=
  MvPowerSeries.subst (fun k : σ => ∑ j : κ, algebraMap ℂ_[p] (MvPowerSeries κ ℂ_[p]) (c k j) * w j) F

def AllSplit (D : D7) (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → P ≠ ⊥ → (p : 𝓞 D.host.E) ∈ P → (D.host.conj : _) • P ≠ P

def IsFrobC (D : D7) (p : ℕ) : Prop :=
  ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})],
    IsArithFrobAt ℤ D.host.conj P

abbrev TVarB (D : D7) (N N' : ℕ) : Type := ZMod 1 × (D.what₂.Tau × Fin N × Fin N')

def tauEmb (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) : D.host.E → ℂ_[p] :=
  fun x => lamC lam (embT D τ x)

def chgB (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E)
    (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (k : D.what₂.Tau × Fin N' × Fin N) (j : TVarB D N N') : ℂ_[p] :=
  if j.2.1 = k.1 then
    ((P' j.2.1).map (tauEmb D lam j.2.1)) k.2.1 j.2.2.2 *
      (((P j.2.1).map (tauEmb D lam j.2.1))⁻¹) j.2.2.1 k.2.2
  else 0

def OrthoBasisW (D : D7) {p : ℕ} [Fact p.Prime] (ρ : D.host.E → ℂ_[p]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (P : Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  LocBasisW D ρ L P ∧ (P.map D.host.conj).transpose * P = 1

def JetTorsionCompatibility (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  (∀ i : D.jet.Sit, ∃ (lam : Qbar →+* ℂ_[(D.jet.loc i).l]) (Po : Pos D (D.jet.loc i).l (D.jet.loc i).d)
      (v : {v // v ∈ Po.V})
      (L : Submodule (𝓞 D.host.E) (Fin (D.jet.loc i).N0 → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin (D.jet.loc i).N1 → D.host.E))
      (P : {v // v ∈ Po.V} → Matrix (Fin (D.jet.loc i).N0) (Fin (D.jet.loc i).N0) D.host.E)
      (P' : {v // v ∈ Po.V} → Matrix (Fin (D.jet.loc i).N1) (Fin (D.jet.loc i).N1) D.host.E)
      (F : MvPowerSeries (D.what₂.Tau × Fin (D.jet.loc i).N1 × Fin (D.jet.loc i).N0) ℂ_[(D.jet.loc i).l])
      (c : ℂ_[(D.jet.loc i).l]), ‖c‖ = 1 ∧ admitted D _ _ L L' ∧
      (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod (D.jet.loc i).d)) L (P v)) ∧
      (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod (D.jet.loc i).d)) L' (P' v)) ∧
      IsComb D T e lam L L' F ∧
      (D.jet.loc i).Th = atLin (fun k (j : ZMod (D.jet.loc i).d × Fin (D.jet.loc i).N0 × Fin (D.jet.loc i).N1) =>
        c * chg D lam Po P P' k (j.1, (v, j.2))) (fun j => MvPowerSeries.X j) F ∧
      ∀ s, D.jetTau i s = letterOf D Po.φ v.1 s) ∧
  (∀ i : D.jet.Sit1, IsFrobC D (D.jet.loc1 i).l ∧
    ∃ (lam : Qbar →+* ℂ_[(D.jet.loc1 i).l]) (τ : D.what₂.Tau)
      (L : Submodule (𝓞 D.host.E) (Fin (D.jet.loc1 i).N0 → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin (D.jet.loc1 i).N1 → D.host.E))
      (P : D.what₂.Tau → Matrix (Fin (D.jet.loc1 i).N0) (Fin (D.jet.loc1 i).N0) D.host.E)
      (P' : D.what₂.Tau → Matrix (Fin (D.jet.loc1 i).N1) (Fin (D.jet.loc1 i).N1) D.host.E)
      (F : MvPowerSeries (D.what₂.Tau × Fin (D.jet.loc1 i).N1 × Fin (D.jet.loc1 i).N0) ℂ_[(D.jet.loc1 i).l])
      (c : ℂ_[(D.jet.loc1 i).l]), ‖c‖ = 1 ∧ admitted D _ _ L L' ∧
      (∀ τ, OrthoBasisW D (tauEmb D lam τ) L (P τ)) ∧ (∀ τ, OrthoBasisW D (tauEmb D lam τ) L' (P' τ)) ∧
      IsComb D T e lam L L' F ∧
      (D.jet.loc1 i).Th = atLin (fun k (j : ZMod 1 × Fin (D.jet.loc1 i).N0 × Fin (D.jet.loc1 i).N1) =>
        c * chgB D lam P P' k (j.1, (τ, j.2))) (fun j => MvPowerSeries.X j) F ∧
      D.jetTau1 i = τ)

end Formalism.MainNotions.TaylorLogMetric
