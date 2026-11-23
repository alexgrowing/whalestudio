import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.BaseEx
import Formalism.LocalToGlobal.Columns.WordFin
import Formalism.LocalToGlobal.GlobalTheory.JetPositivity.DeltaPowTwelveEqDiscr
import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.Ker

structure CarRows (R : Ranks) where
  Tau : Type
  [instTau : Fintype Tau]
  card_Tau : Fintype.card Tau = R.f

attribute [instance] CarRows.instTau

structure Car where
  R : Ranks
  host : Host R
  what₂ : CarRows R
  eTau : what₂.Tau ≃ (R.Psi)

def Car.ofRec (D : D7) : Car := ⟨D.R, D.host, ⟨D.what₂.Tau, D.what₂.card_Tau⟩, D.eTau⟩

def carD (d : Formalism.L2.Col.ColDat) : Car := ⟨d.R, d.host, ⟨d.what₂.Tau, d.what₂.card_Tau⟩, d.eTau⟩

end Formalism.L2.Ker

namespace Formalism.L2.Ker.Cd.TaylorLogMetric

open Formalism.MainNotions.TaylorLogMetric

open NumberField Formalism.BasicNotions Classical
open scoped Pointwise

def chK (D : Car) : DirichletCharacter ℂ D.host.d :=
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  (quadraticChar (ZMod D.host.d)).ringHomComp (Int.castRingHom ℂ)

def logDerivativeAtOne (D : Car) : ℝ :=
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  (deriv (DirichletCharacter.LFunction (chK D)) 1 / DirichletCharacter.LFunction (chK D) 1).re

def logOmVal (D : Car) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.pi / D.host.v) - logDerivativeAtOne D

def fF (D : Car) : ℕ := D.R.f

def embT (D : Car) (τ : D.what₂.Tau) : D.host.E →+* ℂ := D.host.emb (D.eTau τ : D.R.GG)

def homL (D : Car) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) :=
  Submodule.span (𝓞 D.host.E) {A | ∀ x ∈ L, A.mulVec x ∈ L'}

def YYl (D : Car) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) :=
  Submodule.span (𝓞 D.host.E)
    {B | ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ A ∈ homL D L L', B = a • A}

def hYY (D : Car) {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) : D.host.K :=
  Algebra.trace D.host.K D.host.E (∑ i, ∑ j, x i j * D.host.conj (y i j))

def lamOf (D : Car) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : AddSubgroup ℂ :=
  AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * D.host.φ₀ (((c : D.host.K) : D.host.E))}

def IsCurveIdeal (D : Car) (cc : Ideal (𝓞 D.host.K)) : Prop :=
  cc ≠ ⊥ ∧ Nat.Coprime (Ideal.absNorm cc) (2 * D.host.d)

def IsDiscriminantTwelfthRootOfIdealLattice (D : Car) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop :=
  δ ^ 12 = discr (lamOf D cc 1)

structure Tor (D : Car) where
  emb : D.what₂.Tau → D.host.E → ℂ
  abelian₂ : AddSubgroup ℂ

abbrev VC (D : Car) (N N' : ℕ) : Type := D.what₂.Tau → Fin N' → Fin N → ℂ

def tor0 (D : Car) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Tor D :=
  ⟨fun τ => embT D τ, lamOf D cc δ⟩

def embV (D : Car) (T : Tor D) {N N' : ℕ} (A : Matrix (Fin N') (Fin N) D.host.E) : VC D N N' :=
  fun τ i j => T.emb τ (A i j)

def La (D : Car) (T : Tor D) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : AddSubgroup (VC D N N') :=
  AddSubgroup.closure {z | ∃ w ∈ T.abelian₂, ∃ A ∈ YYl D L L', z = w • embV D T A}

def Hf (D : Car) (T : Tor D) {N N' : ℕ} (z w : VC D N N') : ℂ :=
  (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (area T.abelian₂ : ℂ)

def al (D : Car) (T : Tor D) {N N' : ℕ} (x : VC D N N') : ℂ :=
  (-1 : ℂ) ^ (round (Real.sqrt D.host.d / 2 * (Hf D T x x).re))

def U (D : Car) (T : Tor D) {N N' : ℕ} (x : VC D N N') (G : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2)

def ThSp (D : Car) (T : Tor D) {N N' : ℕ} (La' : AddSubgroup (VC D N N')) : Set (VC D N N' → ℂ) :=
  {G | Differentiable ℂ G ∧ ∀ x ∈ La', ∀ z, al D T x * U D T x G z = G z}

def Th (D : Car) (T : Tor D) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Set (VC D N N' → ℂ) :=
  ThSp D T (La D T L L')

def normSq (D : Car) (T : Tor D) {N N' : ℕ} (La' : AddSubgroup (VC D N N'))
    (G : VC D N N' → ℂ) : ℝ :=
  let Fd : Set (VC D N N') :=
    Classical.epsilon (fun Fd => MeasureTheory.IsAddFundamentalDomain La' Fd MeasureTheory.volume)
  ⨍ z in Fd, ‖G z‖ ^ 2 * Real.exp (-Real.pi * (Hf D T z z).re)

def Iop (D : Car) (T : Tor D) {N N' : ℕ} (La₁ La₂ : AddSubgroup (VC D N N'))
    (G : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
    ∑ᶠ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      al D T ((Quotient.out q : La₂) : VC D N N') * U D T ((Quotient.out q : La₂) : VC D N N') G z

def pull (D : Car) (T : Tor D) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (G : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => G (fun τ => (Matrix.conjTranspose (γ'.map (T.emb τ)) * (Matrix.of (z τ)) * γ.map (T.emb τ) : Matrix _ _ ℂ))

abbrev Mono (D : Car) (N N' : ℕ) : Type := (D.what₂.Tau × Fin N' × Fin N) →₀ ℕ

def coordV (D : Car) {N N' : ℕ} (k : D.what₂.Tau × Fin N' × Fin N) : VC D N N' :=
  fun τ i j => if τ = k.1 ∧ i = k.2.1 ∧ j = k.2.2 then 1 else 0

def taylor (D : Car) {N N' : ℕ} (G : VC D N N' → ℂ) (α : Mono D N N') : ℂ :=
  iteratedFDeriv ℂ (Multiset.card α.toMultiset) G 0
      (fun i => coordV D (α.toMultiset.toList.get ⟨i, by simpa using i.2⟩)) /
    (α.prod fun _ n => (n.factorial : ℂ))

def mono (D : Car) {N N' : ℕ} (α : Mono D N N') (z : VC D N N') : ℂ :=
  α.prod fun k n => z k.1 k.2.1 k.2.2 ^ n

def torConj (D : Car) (T : Tor D) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : Tor D :=
  ⟨fun τ x => ρ (liftM M (T.emb τ x)), lamConj M ρ T.abelian₂⟩

def fnConj (D : Car) {N N' : ℕ} (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (G : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => ∑' α : Mono D N N', ρ (liftM M (taylor D G α)) * mono D α z

def DataIn (D : Car) (T : Tor D) (M : IntermediateField ℚ ℂ) : Prop :=
  (∀ τ x, T.emb τ x ∈ M) ∧ g2 T.abelian₂ ∈ M ∧ g3 T.abelian₂ ∈ M

def CoefIn (D : Car) {N N' : ℕ} (G : VC D N N' → ℂ) (M : IntermediateField ℚ ℂ) : Prop :=
  ∀ α, taylor D G α ∈ M

def meanLogNormSq (D : Car) (T : Tor D) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (G : VC D N N' → ℂ) : ℝ :=
  (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (normSq D (torConj D T M ρ) (La D (torConj D T M ρ) L L')
      (fnConj D M ρ G))) / (Module.finrank ℚ M : ℝ)

def mmM (D : Car) (M : IntermediateField ℚ ℂ) [NumberField M] :
    Submodule (𝓞 M) (D.what₂.Tau → M) :=
  Submodule.span (𝓞 M) {v | ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
    v = fun τ => liftM M (embT D τ a)}

def ellT (D : Car) (M : IntermediateField ℚ ℂ) [NumberField M] (τ : D.what₂.Tau) :
    Submodule (𝓞 M) M :=
  (mmM D M).comap (LinearMap.single (𝓞 M) (fun _ : D.what₂.Tau => (M : Type)) τ)

def meanLogOm (D : Car) (Λ : AddSubgroup ℂ) (M : IntermediateField ℚ ℂ) [NumberField M]
    (τ : D.what₂.Tau) : ℝ :=
  let s : M := Classical.epsilon (fun s : M => s ≠ 0 ∧ s ∈ ellT D M τ)
  (2 * Real.log ((((Submodule.span (𝓞 M) {s}).toAddSubgroup.addSubgroupOf
      (ellT D M τ).toAddSubgroup).index : ℕ) : ℝ) -
    ∑ ρ : M →ₐ[ℚ] ℂ, logMet M Λ ρ s) / (Module.finrank ℚ M : ℝ)

abbrev FamE (D : Car) : Type :=
  ∀ (N N' : ℕ), Submodule (𝓞 D.host.E) (Fin N → D.host.E) →
    Submodule (𝓞 D.host.E) (Fin N' → D.host.E) → VC D N N' → ℂ

def admitted (D : Car) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Prop :=
  letI := D.host.cmStar
  Even N ∧ Even N' ∧ IsSDLat D.host.E N L ∧ IsSDLat D.host.E N' L'

def pSer (D : Car) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (G : VC D N N' → ℂ) :
    MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] :=
  fun α => lamC lam (taylor D G α)

def LocBasis (D : Car) {N N' r : ℕ} (p : ℕ) (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E))
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) : Prop :=
  LinearIndependent D.host.K b ∧
  (∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) • b i ∈ Y) ∧
  ∀ y ∈ Y, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : Fin r → 𝓞 D.host.K,
    (s : D.host.E) • y = ∑ i, (((c i : D.host.K) : D.host.E)) • b i

def Orthonormal (D : Car) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) : Prop :=
  ∀ i j, hYY D (b i) (b j) = if i = j then 1 else 0

def atLog (D : Car) {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    MvPowerSeries (Fin r) ℂ_[p] :=
  let W := C • wModel lam Λ
  MvPowerSeries.subst (fun k : D.what₂.Tau × Fin N' × Fin N => ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p])
      (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
      PowerSeries.subst (MvPowerSeries.X i) (flog W wq)) F

def der (D : Car) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (y : Matrix (Fin N') (Fin N) D.host.E)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] :=
  ∑ k : D.what₂.Tau × Fin N' × Fin N,
    algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (lamC lam (embT D k.1 (y k.2.1 k.2.2))) *
      pd k F

def JetsInt (D : Car) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E))
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : Prop :=
  ∀ (n : ℕ) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ i, y i ∈ Y) →
    IsIntP (MvPowerSeries.constantCoeff ((List.ofFn y).foldr (fun y' G => der D lam y' G) F))

def TorsPrime (D : Car) {N N' : ℕ} (p : ℕ) (La' : AddSubgroup (VC D N N')) (t : VC D N N') : Prop :=
  ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ n • t ∈ La'

def EqAt {N : ℕ} (D : Car) (p : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ L, (s : D.host.E) • x ∈ L₁) ∧ ∀ x ∈ L₁, (s : D.host.E) • x ∈ L

def IsComb (D : Car) (T : Tor D) (e : FamE D) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : Prop :=
  ∃ (m : ℕ) (r : Fin m → ℂ_[p]) (t : Fin m → VC D N N')
    (L₁ : Fin m → Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₁' : Fin m → Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    (∀ k, IsIntP (r k)) ∧ (∀ k, TorsPrime D p (La D T L L') (t k)) ∧
    (∀ k, admitted D N N' (L₁ k) (L₁' k) ∧ EqAt D p L (L₁ k) ∧ EqAt D p L' (L₁' k)) ∧
    F = ∑ k, algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (r k) *
      pSer D lam (U D T (t k) (e N N' (L₁ k) (L₁' k)))

def sgm (D : Car) : D.R.GG := ((-1, 1), 1)

def tauSg (D : Car) (τ : D.what₂.Tau) : D.what₂.Tau :=
  if h : (D.eTau τ : D.R.GG) * sgm D ∈ D.R.Psi then D.eTau.symm ⟨_, h⟩ else τ

def Qd (D : Car) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (u : D.what₂.Tau → ℂ_[p]) :
    MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] :=
  ∑ τ : D.what₂.Tau, ∑ a : Fin N', ∑ b : Fin N,
    algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (u τ) *
      MvPowerSeries.X (τ, a, b) * MvPowerSeries.X (tauSg D τ, a, b)

abbrev IdE (D : Car) : Type := Submodule (𝓞 D.host.E) D.host.E

def N1 (D : Car) (𝔞 : IdE D) : Prop :=
  ∃ 𝔟 : IdE D, (∀ x, x ∈ 𝔟 ↔ D.host.conj x ∈ 𝔞) ∧ 𝔞 * 𝔟 = 1

def detId (D : Car) {N : ℕ} (L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : IdE D :=
  Submodule.span (𝓞 D.host.E)
    {x | ∃ A : Matrix (Fin N) (Fin N) D.host.E, (∀ v ∈ L, A.mulVec v ∈ L') ∧ x = A.det}

def IsChi (D : Car) (χ : IdE D → ℂ) : Prop :=
  (∀ 𝔞 𝔟, N1 D 𝔞 → N1 D 𝔟 → χ (𝔞 * 𝔟) = χ 𝔞 * χ 𝔟) ∧
  letI := D.host.cmStar
  ∀ z : unitary D.host.E,
    χ (Submodule.span (𝓞 D.host.E) {(z : D.host.E)}) = ∏ τ : D.what₂.Tau, (embT D τ (z : D.host.E))⁻¹

def qH (D : Car) (T : Tor D) {N N' : ℕ} (x : VC D N N') : ℝ :=
  Real.sqrt D.host.d / 2 * (Hf D T x x).re

def wPh (D : Car) (T : Tor D) {N N' : ℕ} (p : ℕ) (x : VC D N N') : ℂ :=
  if p = 2 then Complex.exp ((Real.pi : ℂ) * Complex.I * (qH D T x : ℂ))
  else Classical.epsilon (fun s : ℂ =>
    ∃ (k : ℕ) (m : ℤ), (p : ℝ) ^ k * qH D T x = (m : ℝ) ∧ s = (-1 : ℂ) ^ m)

def Wop (D : Car) (T : Tor D) {N N' : ℕ} (p : ℕ) (x : VC D N N') (G : VC D N N' → ℂ) :
    VC D N N' → ℂ :=
  fun z => wPh D T p x * U D T x G z

def kap (D : Car) (T : Tor D) {N N' : ℕ} (x y : VC D N N') : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((Hf D T x y).im : ℂ))

def NNBasis (D : Car) (T : Tor D) (δ : ℂ) (p : ℕ) {N N' r : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) : Prop :=
  LocBasis D p (YYl D L L') b ∧ ∀ i, δ • embV D T (b i) ∈ La D T L L'

def IsIdem (D : Car) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (m : ℕ) (ε : 𝓞 D.host.K) : Prop :=
  ‖lamC lam (D.host.φ₀ ((ε : D.host.K) : D.host.E)) - 1‖ ≤ (p : ℝ) ^ (-(m : ℤ)) ∧
  ‖lamC lam (D.host.φ₀ (D.host.conj ((ε : D.host.K) : D.host.E)))‖ ≤ (p : ℝ) ^ (-(m : ℤ))

def liftY (D : Car) (T : Tor D) (δ : ℂ) {N N' r : ℕ} (p n : ℕ) (ε : 𝓞 D.host.K)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Fin r → Fin (p ^ n)) : VC D N N' :=
  δ • embV D T ((((ε : D.host.K) : D.host.E) / (p : D.host.E) ^ n) •
    ∑ i, (((y i : ℕ) : D.host.E)) • b i)

def vecN (D : Car) (T : Tor D) (δ : ℂ) {N N' r : ℕ} (p n : ℕ)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (a : Fin r → Fin (p ^ n)) : VC D N N' :=
  δ • embV D T (∑ i, (((a i : ℕ) : D.host.E)) • b i)

def XiF (D : Car) (T : Tor D) (δ : ℂ) {N N' r : ℕ} (p n : ℕ) [Fact p.Prime] (ε : 𝓞 D.host.K)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ)
    (G : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => ((p : ℂ) ^ (n * r))⁻¹ * ∑ a : Fin r → Fin (p ^ n), Φ (fun i => (((a i : ℕ) : ℤ_[p]))) *
    ∑ y : Fin r → Fin (p ^ n), (kap D T (vecN D T δ p n b a) (liftY D T δ p n ε b y))⁻¹ *
      Wop D T p (liftY D T δ p n ε b y) G z

def pairN (D : Car) {N N' r p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Matrix (Fin N') (Fin N) D.host.E)
    (a : Fin r → ℤ_[p]) : ℂ_[p] :=
  Ω⁻¹ * ∑ i, zc (a i) * lamC lam (D.host.φ₀ ((hYY D y (b i) : D.host.K) : D.host.E))

def jet (D : Car) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {n : ℕ}
    (y : Fin n → Matrix (Fin N') (Fin N) D.host.E)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : ℂ_[p] :=
  MvPowerSeries.constantCoeff ((List.ofFn y).foldr (fun y' G => der D lam y' G) F)

def EqAway {N : ℕ} (D : Car) (p : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  ∃ k : ℕ, (∀ x ∈ L, ((p : D.host.E) ^ k) • x ∈ L₁) ∧ ∀ x ∈ L₁, ((p : D.host.E) ^ k) • x ∈ L

def posG (D : Car) (φ : D.R.GG) {d : ℕ} (τ0 : D.what₂.Tau) (s : ZMod d) :
    D.R.GG :=
  (D.eTau τ0 : D.R.GG) * φ ^ s.val

def letterOf (D : Car) (φ : D.R.GG) {d : ℕ} (τ0 : D.what₂.Tau) (s : ZMod d) : D.what₂.Tau :=
  if h : posG D φ τ0 s ∈ D.R.Psi then D.eTau.symm ⟨_, h⟩
  else if h' : D.R.cc * posG D φ τ0 s ∈ D.R.Psi then D.eTau.symm ⟨_, h'⟩
  else τ0

structure Pos (D : Car) (p d : ℕ) where
  φ : D.R.GG
  frob : ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})],
    IsArithFrobAt ℤ (D.host.sigmaOf φ) P
  d_eq : d = orderOf φ
  V : Finset D.what₂.Tau
  bij : Function.Bijective (fun x : {v // v ∈ V} × ZMod d => letterOf D φ x.1.1 x.2)

def posEmb (D : Car) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (φ : D.R.GG) {d : ℕ}
    (τ0 : D.what₂.Tau) (s : ZMod d) : D.host.E → ℂ_[p] :=
  fun x => lamC lam (D.host.emb (posG D φ τ0 s) x)

def LocBasisW (D : Car) {p : ℕ} [Fact p.Prime] (ρ : D.host.E → ℂ_[p]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (P : Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  P.det ≠ 0 ∧ (∀ a, ∃ s : 𝓞 D.host.E, ‖ρ (s : D.host.E)‖ = 1 ∧ s • P.transpose a ∈ L) ∧
  ∀ x ∈ L, ∃ s : 𝓞 D.host.E, ‖ρ (s : D.host.E)‖ = 1 ∧ ∃ c : Fin N → 𝓞 D.host.E,
    s • x = ∑ a, c a • P.transpose a

abbrev TVar (D : Car) {p d : ℕ} (Po : Pos D p d) (N N' : ℕ) : Type :=
  ZMod d × ({v // v ∈ Po.V} × Fin N × Fin N')

def chg (D : Car) {p d : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Po : Pos D p d) {N N' : ℕ}
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

def AllSplit (D : Car) (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → P ≠ ⊥ → (p : 𝓞 D.host.E) ∈ P → (D.host.conj : _) • P ≠ P

def IsFrobC (D : Car) (p : ℕ) : Prop :=
  ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})],
    IsArithFrobAt ℤ D.host.conj P

abbrev TVarB (D : Car) (N N' : ℕ) : Type := ZMod 1 × (D.what₂.Tau × Fin N × Fin N')

def tauEmb (D : Car) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) : D.host.E → ℂ_[p] :=
  fun x => lamC lam (embT D τ x)

def chgB (D : Car) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E)
    (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (k : D.what₂.Tau × Fin N' × Fin N) (j : TVarB D N N') : ℂ_[p] :=
  if j.2.1 = k.1 then
    ((P' j.2.1).map (tauEmb D lam j.2.1)) k.2.1 j.2.2.2 *
      (((P j.2.1).map (tauEmb D lam j.2.1))⁻¹) j.2.2.1 k.2.2
  else 0

def OrthoBasisW (D : Car) {p : ℕ} [Fact p.Prime] (ρ : D.host.E → ℂ_[p]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (P : Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  LocBasisW D ρ L P ∧ (P.map D.host.conj).transpose * P = 1

def vec22 (D : Car) (T : Tor D) (e : FamE D) : Prop :=
  ∀ N N' L L', admitted D N N' L L' →
    e N N' L L' ∈ Th D T L L' ∧ e N N' L L' ≠ 0 ∧
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ CoefIn D (e N N' L L') M

def per22 (D : Car) (T : Tor D) : Prop :=
  ∀ (M : IntermediateField ℚ ℂ) [NumberField M], DataIn D T M →
    ∀ τ : D.what₂.Tau, meanLogOm D T.abelian₂ M τ = logOmVal D

def th22 (D : Car) (T : Tor D) (C : ℝ) (e : FamE D) : Prop :=
  (∀ N N' L₁ L₁' L₂ L₂', admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
    normSq D T (La D T L₁ L₁') (e N N' L₁ L₁') = normSq D T (La D T L₂ L₂') (e N N' L₂ L₂')) ∧
  (∀ Lsc : ℝ, Real.log D.host.v + |logDerivativeAtOne D| ≤ Lsc →
    ∀ N N' L L', admitted D N N' L L' →
      ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], DataIn D T M → CoefIn D (e N N' L L') M →
        meanLogNormSq D T L L' M (e N N' L L') ≤ C * (fF D : ℝ) * (N : ℝ) * (N' : ℝ) * Lsc) ∧
  (∀ N N' L₁ L₁' L₂ L₂', admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
    ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], DataIn D T M →
      CoefIn D (e N N' L₁ L₁') M → CoefIn D (e N N' L₂ L₂') M → ∀ ρ : M →ₐ[ℚ] ℂ,
        normSq D (torConj D T M ρ) (La D (torConj D T M ρ) L₁ L₁') (fnConj D M ρ (e N N' L₁ L₁')) =
          normSq D (torConj D T M ρ) (La D (torConj D T M ρ) L₂ L₂') (fnConj D M ρ (e N N' L₂ L₂'))) ∧
  (∀ N N' L L', admitted D N N' L L' → ∀ x : VC D N N',
    normSq D T (La D T L L') (U D T x (e N N' L L')) = normSq D T (La D T L L') (e N N' L L'))

def eq22 (D : Car) (T : Tor D) (χ : IdE D → ℂ) (e : FamE D) : Prop :=
  letI := D.host.cmStar
  (∀ N N' (L : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E),
      pull D T (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
          (e N N' L.1 L'.1) =
        e N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L.1)
          (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L'.1)) ∧
  (∀ N N' (L : SDLat D.host.E N) (L' L'' : SDLat D.host.E N'), Even N → Even N' →
    e N N' L.1 L''.1 = fun z => (χ (detId D L'.1 L''.1)) ^ (-((N / 2 : ℕ) : ℤ)) *
      Iop D T (La D T L.1 L'.1) (La D T L.1 L''.1) (e N N' L.1 L'.1) z) ∧
  (∀ N N' (L L₁ : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    e N N' L₁.1 L'.1 = fun z => (χ (detId D L.1 L₁.1)) ^ (((N' / 2 : ℕ) : ℤ)) *
      Iop D T (La D T L.1 L'.1) (La D T L₁.1 L'.1) (e N N' L.1 L'.1) z)

def DualB (D : Car) {N : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  ∀ τ, ((P (tauSg D τ)).map D.host.conj).transpose * P τ = 1

def zB (D : Car) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (τ : D.what₂.Tau) (a : Fin N') (b : Fin N) : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] :=
  ∑ i : Fin N', ∑ j : Fin N,
    algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p])
      ((((P' τ).map (tauEmb D lam τ))⁻¹) a i * ((P τ).map (tauEmb D lam τ)) j b) * MvPowerSeries.X (τ, i, j)

def QdB (D : Car) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (u : D.what₂.Tau → ℂ_[p])
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) :
    MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] :=
  ∑ τ : D.what₂.Tau, ∑ a : Fin N', ∑ b : Fin N,
    algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (u τ) *
      zB D lam P P' τ a b * zB D lam P P' (tauSg D τ) a b

def int22 (D : Car) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' →
    (p ≠ D.host.d → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], IsComb D T e lam L L' F →
      (∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (r : ℕ)
          (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq → LocBasis D p (YYl D L L') b →
        Orthonormal D b →
        IntegralMv (atLog D lam T.abelian₂ C wq b F * ePh lam T.abelian₂ C wq r)) ∧
      JetsInt D lam (YYl D L L') F ∧
      ((p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) →
        ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (r : ℕ)
          (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq → LocBasis D p (YYl D L L') b →
        IntegralMv (atLog D lam T.abelian₂ C wq b F))) ∧
    (p = D.host.d →
      ∃ S : ℂ_[p], ‖S‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) ∧
        ∃ u : D.what₂.Tau → ℂ_[p], (∀ τ, ‖u τ‖ = 1) ∧ (∀ τ, u (tauSg D τ) = u τ) ∧
          ∀ (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E)
            (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E),
          (∀ τ, LocBasisW D (tauEmb D lam τ) L (P τ)) → (∀ τ, LocBasisW D (tauEmb D lam τ) L' (P' τ)) →
          DualB D P → DualB D P' →
          ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], IsComb D T e lam L L' F →
          ∃ F₀, F = expMv (-(algebraMap ℂ_[p] _ S) * QdB D lam u P P') * F₀ ∧
            JetsInt D lam (YYl D L L') F₀)

def mom22 (D : Car) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    (p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) → Nat.Coprime (Ideal.absNorm cc) p →
    ∃ Ω : ℂ_[p], IsOmP lam (tor0 D cc δ).abelian₂ Ω ∧
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (r : ℕ)
      (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
      admitted D N N' L L' → NNBasis D (tor0 D cc δ) δ p L L' b →
      ∃ μ : C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p], ‖μ‖ ≤ 1 ∧
        (∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[p], ℂ_[p])),
          (∀ a, g a = ∏ j, pairN D lam Ω b (y j) a) →
          jet D lam y (pSer D lam (e N N' L L')) = μ g) ∧
        ∀ (n : ℕ) (ε : 𝓞 D.host.K) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ),
          IsIdem D lam (2 * n + 2) ε → (∀ a, Φ a ∈ Qbar) → FactorsMod n Φ →
          ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[p], ℂ_[p])),
            (∀ a, g a = lamC lam (Φ a) * ∏ j, pairN D lam Ω b (y j) a) →
            jet D lam y (pSer D lam (XiF D (tor0 D cc δ) δ p n ε b Φ (e N N' L L'))) = μ g

def LargerSupportMomentCondition (D : Car) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    (p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) → Nat.Coprime (Ideal.absNorm cc) p →
    ∀ (N N' : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (r : ℕ)
      (b b₁ : Fin r → Matrix (Fin N') (Fin N) D.host.E) (c : Fin r → Fin r → D.host.K),
      admitted D N N' L L' → admitted D N N' L₁ L₂ → EqAway D p L L₁ → EqAway D p L' L₂ →
      NNBasis D (tor0 D cc δ) δ p L L' b → NNBasis D (tor0 D cc δ) δ p L₁ L₂ b₁ →
      (∀ j, b j = ∑ i, ((c i j : D.host.K) : D.host.E) • b₁ i) →
      (∀ i j, ‖lamC lam (D.host.φ₀ (D.host.conj ((c i j : D.host.K) : D.host.E)))‖ ≤ 1) →
      ∀ (n : ℕ) (ε : 𝓞 D.host.K) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ),
        IsIdem D lam (2 * n + 2) ε → FactorsMod n Φ →
        (∀ a, Φ a = if ∃ x : Fin r → ℤ_[p], ∀ i, zc (a i) =
            ∑ j, lamC lam (D.host.φ₀ (D.host.conj ((c i j : D.host.K) : D.host.E))) * zc (x j)
          then 1 else 0) →
        ∃ κ : ℂ, κ ∈ Qbar ∧ ‖lamC lam κ‖ = 1 ∧
          XiF D (tor0 D cc δ) δ p n ε b₁ Φ (e N N' L₁ L₂) = fun z => κ * e N N' L L' z

def sE (D : Car) {N N' p d : ℕ} [Fact p.Prime] (Po : Pos D p d) (v : {v // v ∈ Po.V}) (e : ZMod d)
    (a : Fin N) (b : Fin N') : MvPowerSeries (TVar D Po N N') ℂ_[p] :=
  fun α => ∑ l ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if α = Finsupp.single ((e - 2 * (l : ZMod d), (v, a, b)) : TVar D Po N N') ((p ^ 2) ^ l)
    then (-1 : ℂ_[p]) ^ l else 0

def hh (D : Car) {N N' p d : ℕ} [Fact p.Prime] [NeZero d] (Po : Pos D p d) (v : {v // v ∈ Po.V})
    (u : ZMod d → ℂ_[p]) : MvPowerSeries (TVar D Po N N') ℂ_[p] :=
  ∑ s : ZMod d, algebraMap ℂ_[p] (MvPowerSeries (TVar D Po N N') ℂ_[p]) (u s) *
    ∑ a : Fin N, ∑ b : Fin N', sE D Po v s a b ^ p * sE D Po v (s + 1) a b

def InProd (D : Car) {N N' p d : ℕ} [Fact p.Prime] (Po : Pos D p d)
    (h : {v // v ∈ Po.V} → MvPowerSeries (TVar D Po N N') ℂ_[p])
    (F : MvPowerSeries (TVar D Po N N') ℂ_[p]) : Prop :=
  ∃ g : ({v // v ∈ Po.V} → ℕ) → MvPowerSeries (TVar D Po N N') ℂ_[p], (∀ i, IntegralMv (g i)) ∧
    ∀ α, MvPowerSeries.coeff α F =
      ∑ i ∈ Fintype.piFinset (fun _ : {v // v ∈ Po.V} => Finset.range ((α.sum fun _ k => k) + 1)),
        MvPowerSeries.coeff α
          (algebraMap ℂ_[p] (MvPowerSeries (TVar D Po N N') ℂ_[p]) (∏ v, ((p : ℂ_[p]) ^ i v)⁻¹) *
            (∏ v, h v ^ i v) * g i)

def str22 (D : Car) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → AllSplit D p →
    ∃ ep : ℂ_[p], InW ep ∧ ‖ep‖ = 1 ∧
    ∀ (d : ℕ) [NeZero d] (Po : Pos D p d) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (P : {v // v ∈ Po.V} → Matrix (Fin N) (Fin N) D.host.E)
      (P' : {v // v ∈ Po.V} → Matrix (Fin N') (Fin N') D.host.E) (ϖ : ℂ_[p]),
      admitted D N N' L L' → (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L (P v)) →
      (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L' (P' v)) →
      ϖ ^ (p ^ 2 - 1) = (p : ℂ_[p]) →
      ∃ u : {v // v ∈ Po.V} → ZMod d → ℂ_[p], (∀ v s, IsIntP (u v s)) ∧
        ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], IsComb D T e lam L L' F →
        ∀ h' : {v // v ∈ Po.V} → MvPowerSeries (TVar D Po N N') ℂ_[p],
          (∀ v, ∃ G : MvPowerSeries (TVar D Po N N') ℂ_[p], IntegralMv G ∧ MvPowerSeries.constantCoeff G = 0 ∧
            h' v = hh D Po v (u v) + algebraMap ℂ_[p] _ (p : ℂ_[p]) * G) →
          InProd D Po h' (atLin (fun k j => ep * chg D lam Po P P' k j * ϖ)
            (fun j => MvPowerSeries.X j) F)

def adm1 (D : Car) : Prop :=
  (∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭.ramificationIdxIn (𝓞 D.host.E) = 1) ∧
  (∀ x : D.host.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → Algebra.norm D.host.K x = 1) ∧
  (∀ p : ℕ, p.Prime → p ∣ D.host.condN →
    ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsPrime → 𝔭.LiesOver (Ideal.span {(p : ℤ)}) →
      (Ideal.primesOver 𝔭 (𝓞 D.host.E)).ncard = 2) ∧
  (∀ p : ℕ, p.Prime → p ∣ D.host.QS * D.host.q →
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.K)).ncard = 2) ∧
  (∀ 𝔭 : Ideal (𝓞 D.host.K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 1 < 𝔭.ramificationIdxIn (𝓞 D.host.E) →
    ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.K) ∈ 𝔭) ∧
  (∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (D.host.d : 𝓞 D.host.E) ∈ P →
    ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E,
      ((∀ x : 𝓞 D.host.E, ∃ y ∈ P, (y : D.host.E) = σ (x : D.host.E) - (x : D.host.E)) ↔
        (D.host.galE σ = 1 ∨
          D.host.galE σ = ((1, -1), 1))))

def AdmittedStatements (D : Car) : Prop := adm1 D

def aux₃ (D : Car) (C : ℝ) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    per22 D (tor0 D cc δ) ∧ (∃ χ, IsChi D χ) ∧
    ∀ χ, IsChi D χ →
    ∃ e : FamE D, vec22 D (tor0 D cc δ) e ∧ th22 D (tor0 D cc δ) C e ∧ eq22 D (tor0 D cc δ) χ e ∧
      int22 D (tor0 D cc δ) e ∧ mom22 D cc δ e ∧ LargerSupportMomentCondition D cc δ e ∧ str22 D (tor0 D cc δ) e

def Stmt (D : Car) (C : ℝ) : Prop := AdmittedStatements D → aux₃ D C

end Formalism.L2.Ker.Cd.TaylorLogMetric

namespace Formalism.L2.Ker.Cd

open NumberField Formalism.BasicNotions Classical

def StandardLatticesGL3.stdL (D : Car) (N : ℕ) : Submodule (𝓞 D.host.E) (Fin N → D.host.E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)

def GL3Theta.IsTwoTorsionPointUnkilled (D : Car) (Λ : AddSubgroup ℂ) (t : ℂ) : Prop :=
  2 * t ∈ Λ ∧ ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * t ∉ Λ ∧
    ((1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * t ∉ Λ

open scoped BigOperators ComplexConjugate Pointwise
open Formalism.L2.Ker.Base (Comm)

open Formalism.L2.Th1.H (Sesq matH stdH stdLat alphaQ kernel4 tens4 StdData pow4 imgLat inter opU)
open Formalism.MainNotions

section Gen

variable (L : PeriodPair) (ω₀ : ℂ) (c : ℝ) {n : Type} [Fintype n] [DecidableEq n]

end Gen

section Arith

variable (D : Car)

def SplitK (p : ℕ) : Prop := p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1

abbrev IsoK : Type := IsoKG D.host.K D.host.E D.host.conj D.what₂.Tau

variable {D}

def IsoK.AtP (γ : IsoK D) (p : ℕ) : Prop :=
  (∀ x : Fin 4 → D.host.E, (∀ a, x a ∈ D.host.AA0) → ∃ s : ℕ, Nat.Coprime s p ∧
    ∀ w, (s : D.host.K) * γ.g x w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) ∧
  ∀ v : Fin 4 × D.what₂.Tau → D.host.K, (∀ w, v w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) →
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ a, (s : D.host.E) * γ.g.symm v a ∈ D.host.AA0

def IsoK.detRel (γ γ₀ : IsoK D) : D.host.K :=
  LinearMap.det ((γ₀.g.symm.trans γ.g : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] _) :
    (Fin 4 × D.what₂.Tau → D.host.K) →ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K))

def ordK (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K)) (x : D.host.K) : ℤ :=
  -WithZero.log (𝔭.valuation D.host.K x)

structure KapChoice (γ₀ : IsoK D) where
  pp : ℕ → IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K)
  pp_over : ∀ p, p.Prime → SplitK D p → ((p : ℕ) : 𝓞 D.host.K) ∈ (pp p).asIdeal
  pi : ℕ → 𝓞 D.host.K
  pi_gen : ∀ p, p.Prime → SplitK D p → (pp p).asIdeal ^ classNumber D.host.K = Ideal.span {pi p}
  gaP : ℕ → IsoK D
  gaP_at : ∀ p, p.Prime → SplitK D p → (gaP p).AtP p
  rt : ℕ → ℂ
  rt_pow : ∀ p, p.Prime → SplitK D p → rt p ^ (2 * classNumber D.host.K)
    = D.host.φ₀ (((pi p : 𝓞 D.host.K) : D.host.K) : D.host.E)
      / D.host.φ₀ (D.host.conj (((pi p : 𝓞 D.host.K) : D.host.K) : D.host.E))

def KapChoice.yP {γ₀ : IsoK D} (k : KapChoice γ₀) (p : ℕ) : ℤ := ordK (k.pp p) ((k.gaP p).detRel γ₀)

def KapChoice.kappa {γ₀ : IsoK D} (k : KapChoice γ₀) : ℂ :=
  ∏ᶠ p : {p : ℕ // p.Prime ∧ SplitK D p}, k.rt p ^ (-(k.yP p))

def KapChoice.YFinite {γ₀ : IsoK D} (k : KapChoice γ₀) : Prop :=
  {p : ℕ | p.Prime ∧ SplitK D p ∧ k.yP p ≠ 0}.Finite

def YIndep (γ₀ : IsoK D) : Prop :=
  ∀ (p : ℕ) (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K)) (γ γ' : IsoK D), p.Prime → SplitK D p →
    ((p : ℕ) : 𝓞 D.host.K) ∈ 𝔭.asIdeal → γ.AtP p → γ'.AtP p → ordK 𝔭 (γ.detRel γ₀) = ordK 𝔭 (γ'.detRel γ₀)

def lamMM (D : Car) (Λ : AddSubgroup ℂ) : AddSubgroup (D.what₂.Tau → ℂ) :=
  AddSubgroup.closure {z | ∃ w ∈ Λ, ∃ a ∈ D.host.AA0, z = fun τ => w * TaylorLogMetric.embT D τ a}

end Arith

section Fam

variable {D : Car}

structure Base (D : Car) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) where
  L : PeriodPair
  lat : L.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ
  ω₀ : ℂ
  t0 : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) (ω₀ / 2)
  γ₀ : IsoK D
  gC : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)
  gC_spec : ∀ x : Fin 4 → D.host.E, gC (fun w => TaylorLogMetric.embT D w.2 (x w.1))
    = fun w => D.host.φ₀ ((γ₀.g x w : D.host.K) : D.host.E)
  kc : KapChoice γ₀

namespace Base

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

def cq (_B : Base D cc δ) : ℝ := Real.sqrt D.host.d / 2

def lamM (_B : Base D cc δ) : AddSubgroup (D.what₂.Tau → ℂ) := lamMM D (TaylorLogMetric.lamOf D cc δ)

def th0 : ℂ → ℂ := Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2)

def kappa : ℂ := B.kc.kappa

def StdOK : Prop := Ker.StdOK B.L B.ω₀ B.cq B.lamM B.gC

def IsThMM (θ : (D.what₂.Tau → ℂ) → ℂ) : Prop := IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa θ

def thMM : (D.what₂.Tau → ℂ) → ℂ := thM B.L B.ω₀ B.cq B.lamM B.gC B.kappa

def thZero (N N' : ℕ) : TaylorLogMetric.VC D N N' → ℂ := tensPow B.thMM N N'

abbrev tor (_B : Base D cc δ) : TaylorLogMetric.Tor D := TaylorLogMetric.tor0 D cc δ

def eY (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : TaylorLogMetric.VC D N N' → ℂ :=
  TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L L') (B.thZero N N')

def thHalf (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : TaylorLogMetric.VC D N N' → ℂ :=
  TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N'))
    (B.thZero N N')

def thMoved (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : TaylorLogMetric.VC D N N' → ℂ :=
  TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L L') (B.thHalf N N' L)

def chiFac (χ : TaylorLogMetric.IdE D → ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : ℂ :=
  χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) ^ (((N' / 2 : ℕ) : ℤ)) * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N') L') ^ (-((N / 2 : ℕ) : ℤ))

def eNat (χ : TaylorLogMetric.IdE D → ℂ) : TaylorLogMetric.FamE D :=
  fun N N' L L' z => chiFac χ N N' L L' * B.thMoved N N' L L' z

def AreaOK : Prop := TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L

def Lat0OK (N N' : ℕ) : Prop :=
  TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat B.lamM N N'

def LatOK (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Prop :=
  Formalism.L2.Th1.H.IsSelfDual (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.La D B.tor L L') ∧
  Formalism.L2.Th1.H.IsSemiChar (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.La D B.tor L L')
    (TaylorLogMetric.al D B.tor)

def ThZeroMem (N N' : ℕ) : Prop :=
  B.thZero N N' ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
    (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))

def QInt0 (N N' : ℕ) : Prop :=
  ∀ x ∈ TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'), ∃ m : ℤ,
    Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D B.tor x x).re = (m : ℝ)

def QIntAll : Prop :=
  ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' → ∀ x ∈ TaylorLogMetric.La D B.tor L L', ∃ m : ℤ,
    Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D B.tor x x).re = (m : ℝ)

def ThZeroSpans (N N' : ℕ) : Prop :=
  ∀ F ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
    (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')), ∃ a : ℂ, F = a • B.thZero N N'

def LatAll : Prop :=
  (∀ N N' L L', TaylorLogMetric.admitted D N N' L L' → B.LatOK N N' L L') ∧
  ∀ N N' L₁ L₁' L₂ L₂', TaylorLogMetric.admitted D N N' L₁ L₁' → TaylorLogMetric.admitted D N N' L₂ L₂' →
    Comm (TaylorLogMetric.La D B.tor L₁ L₁') (TaylorLogMetric.La D B.tor L₂ L₂')

def VecP (χ : TaylorLogMetric.IdE D → ℂ) : Prop := TaylorLogMetric.vec22 D B.tor (B.eNat χ)

def ThP (C : ℝ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop := TaylorLogMetric.th22 D B.tor C (B.eNat χ)

def EqP (χ : TaylorLogMetric.IdE D → ℂ) : Prop := TaylorLogMetric.eq22 D B.tor χ (B.eNat χ)

def IntP (χ : TaylorLogMetric.IdE D → ℂ) : Prop := TaylorLogMetric.int22 D B.tor (B.eNat χ)

def MomP (χ : TaylorLogMetric.IdE D → ℂ) : Prop := TaylorLogMetric.mom22 D cc δ (B.eNat χ) ∧ TaylorLogMetric.LargerSupportMomentCondition D cc δ (B.eNat χ)

def StrP (χ : TaylorLogMetric.IdE D → ℂ) : Prop := TaylorLogMetric.str22 D B.tor (B.eNat χ)

def LateralTheory (C : ℝ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  B.VecP χ ∧ B.ThP C χ ∧ B.EqP χ ∧ B.IntP χ ∧ B.MomP χ ∧ B.StrP χ

def SignP : Prop :=
  ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' → B.thMoved N N' L L' = B.eY N N' L L' ∨ B.thMoved N N' L L' = -B.eY N N' L L'

def OrderP : Prop :=
  ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' → B.thMoved N N' L L' =
    TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') (TaylorLogMetric.La D B.tor L L')
      (TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L')
        (B.thZero N N'))

end Base

def BaseExists (D : Car) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), TaylorLogMetric.IsCurveIdeal D cc → ∀ δ : ℂ, δ ≠ 0 → Nonempty (Base D cc δ)

def GCUnique (D : Car) : Prop :=
  ∀ (γ₀ : IsoK D) (g g' : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)),
    (∀ x : Fin 4 → D.host.E, g (fun w => TaylorLogMetric.embT D w.2 (x w.1)) = fun w => D.host.φ₀ ((γ₀.g x w : D.host.K) : D.host.E)) →
    (∀ x : Fin 4 → D.host.E, g' (fun w => TaylorLogMetric.embT D w.2 (x w.1)) = fun w => D.host.φ₀ ((γ₀.g x w : D.host.K) : D.host.E)) →
    g = g'

end Fam

open Formalism.MainNotions

section HostFacts

variable (D : Car)

def thetaC : ℂ := (1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2

def KQuad : Prop := Module.finrank ℚ D.host.K = 2

def ConjOnK : Prop := PI.KerIso.IsConj D.host.K D.host.conj

def TrPos : Prop := ∀ x : D.host.E, x ≠ 0 → 0 < Algebra.trace ℚ D.host.E (x * D.host.conj x)

def CardTau : Prop := Fintype.card D.what₂.Tau = Module.finrank D.host.K D.host.E

def EmbInj : Prop := Function.Injective (TaylorLogMetric.embT D)

def EmbOnK : Prop :=
  ∀ (τ : D.what₂.Tau) (k : D.host.K), TaylorLogMetric.embT D τ (algebraMap D.host.K D.host.E k) = D.host.φ₀ (k : D.host.E)

def PhiNonReal : Prop := ∃ k : D.host.K, (D.host.φ₀ (k : D.host.E)).im ≠ 0

def DMod8 : Prop := D.host.d % 8 = 7

def SqrtInK : Prop :=
  ∃ s : D.host.K, s * s = -(D.host.d : D.host.K) ∧
    D.host.conj (algebraMap D.host.K D.host.E s) = -algebraMap D.host.K D.host.E s

def LatStable : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), ∀ w ∈ TaylorLogMetric.lamOf D cc δ, thetaC D * w ∈ TaylorLogMetric.lamOf D cc δ

def ConjIdeal : Prop :=
  ∀ x : 𝓞 D.host.E, x ∈ D.host.conj • D.host.𝔟 ↔ ∃ y ∈ D.host.𝔟, D.host.conj (y : D.host.E) = (x : D.host.E)

def HostFacts : Prop :=
  KQuad D ∧ ConjOnK D ∧ TrPos D ∧ CardTau D ∧ EmbInj D ∧ EmbOnK D ∧ PhiNonReal D ∧ DMod8 D ∧ SqrtInK D ∧ LatStable D ∧ ConjIdeal D

def MMSelfDual : Prop := PI.KerIso.SelfDualI D.host.K D.host.conj D.host.AA0

def SplitKSplits : Prop := ∀ p : ℕ, p.Prime → SplitK D p → PI.KerIso.SplitsAt D.host.K D.host.conj p

def GammaZeroExists : Prop :=
  ∃ (γ₀ : IsoK D) (gC : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)),
    ∀ x : Fin 4 → D.host.E, gC (fun w => TaylorLogMetric.embT D w.2 (x w.1)) = fun w => D.host.φ₀ ((γ₀.g x w : D.host.K) : D.host.E)

def GammaPExists : Prop := ∀ p : ℕ, p.Prime → SplitK D p → ∃ γ : IsoK D, γ.AtP p

def PeriodExists : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∃ L : PeriodPair, L.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ

def TZeroExists : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∃ t : ℂ, GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t

end HostFacts

open IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H

section Seam

open Formalism.MainNotions

structure Seam (D : Car) (X : Fields) where
  iE : X.E ≃+* D.host.E
  iT : X.Tau ≃ D.what₂.Tau
  σ₀ : X.K →+* ℂ

variable {D : Car} {X : Fields} (s : Seam D X)

def Seam.Ok : Prop :=
  (∀ τ x, s.σ₀ (X.emb τ x) = TaylorLogMetric.embT D (s.iT τ) (s.iE x)) ∧ ∀ x, s.iE (star x) = D.host.conj (s.iE x)

def Seam.lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) : Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
  Submodule.span (𝓞 D.host.E) ((fun (x : Sp X.E n) (i : Fin n) => s.iE (x i)) '' (N : Set (Sp X.E n)))

def IsDgen (D : Car) (cD : D.what₂.Tau → ℂ) : Prop :=
  ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M), (∀ τ x, TaylorLogMetric.embT D τ x ∈ M) ∧ ∀ τ, ∃ s : M, (s : ℂ) = cD τ ∧
    TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {s}

def ambOf {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) : Amb X where
  σ₀ := s.σ₀
  δ := δ
  d := D.host.d
  sc := (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹
  AA := Submodule.span (𝓞 X.E) {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}
  cD τ := cD (s.iT τ)
  e a b N N' z := B.eNat χ a b (s.lat N) (s.lat N') fun τ => z (s.iT.symm τ)
  chiF a b N N' := Base.chiFac χ a b (s.lat N) (s.lat N')

end Seam

end Formalism.L2.Ker.Cd

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

def CMTransitive (D : Car) : Prop :=
  (∀ σ : ℂ ≃+* ℂ, ∀ 𝔞 : Ideal (𝓞 D.host.K), 𝔞 ≠ ⊥ →
    ∃ 𝔟 : Ideal (𝓞 D.host.K), 𝔟 ≠ ⊥ ∧ σ (jL (lamOf D 𝔞 1)) = jL (lamOf D 𝔟 1)) ∧
  ∀ 𝔞 𝔟 : Ideal (𝓞 D.host.K), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ →
    ∃ σ : ℂ ≃+* ℂ, (∀ x : D.host.K, σ (D.host.φ₀ (x : D.host.E)) = D.host.φ₀ (x : D.host.E)) ∧
      σ (jL (lamOf D 𝔞 1)) = jL (lamOf D 𝔟 1)

def CMConjEmb (D : Car) : Prop :=
  ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (𝔞 : Ideal (𝓞 D.host.K)), 𝔞 ≠ ⊥ →
    ∀ h : jL (lamOf D 𝔞 1) ∈ M,
      ∃ 𝔟 : Ideal (𝓞 D.host.K), 𝔟 ≠ ⊥ ∧ ρ ⟨jL (lamOf D 𝔞 1), h⟩ = jL (lamOf D 𝔟 1)

def DedekindFactor (D : Car) : Prop :=
  ∀ s : ℂ, 1 < s.re →
    NumberField.dedekindZeta D.host.K s =
      riemannZeta s * (haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
        DirichletCharacter.LFunction (chK D) s)

def ThetaNormIndependent (D : Car) (T : Tor D) (e : FamE D) : Prop :=
  ∀ N N' L₁ L₁' L₂ L₂', admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
    normSq D T (La D T L₁ L₁') (e N N' L₁ L₁') = normSq D T (La D T L₂ L₂') (e N N' L₂ L₂')

def th22U (D : Car) (T : Tor D) (e : FamE D) : Prop :=
  ∀ N N' L L', admitted D N N' L L' → ∀ x : VC D N N',
    normSq D T (La D T L L') (U D T x (e N N' L L')) = normSq D T (La D T L L') (e N N' L L')

def LinkPer : Prop :=
  ∀ D : Car, KroneckerLimit → Uniformization → CMTransitive D → DedekindFactor D →
    ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      per22 D (tor0 D cc δ)

def LinkChi : Prop :=
  ∀ D : Car, AdmittedStatements D → ∃ χ, IsChi D χ

def LinkThU : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ N N' L L', admitted D N N' L L' → ∀ G ∈ Th D (tor0 D cc δ) L L', ∀ x : VC D N N',
      normSq D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (U D (tor0 D cc δ) x G) =
        normSq D (tor0 D cc δ) (La D (tor0 D cc δ) L L') G

def LinkThUFam : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ e : FamE D, vec22 D (tor0 D cc δ) e → th22U D (tor0 D cc δ) e

def LinkThIndep : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (χ : IdE D → ℂ) (e : FamE D), IsChi D χ → vec22 D (tor0 D cc δ) e →
      eq22 D (tor0 D cc δ) χ e → ThetaNormIndependent D (tor0 D cc δ) e

theorem theta_norm_independent_of_bounds (D : Car) (T : Tor D) (C : ℝ) (e : FamE D) (h : th22 D T C e) :
    ThetaNormIndependent D T e := h.1

theorem theta_norm_unitary_invariant_of_bounds (D : Car) (T : Tor D) (C : ℝ) (e : FamE D) (h : th22 D T C e) :
    th22U D T e := h.2.2.2

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

namespace Formalism.L2.Ker

open Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.Jets

section OverColDat

variable (d : ColDat)

def seamD : Cd.Seam (carD d) d.X := ⟨RingEquiv.refl _, Equiv.refl _, d.σ₀⟩

structure AmbIn where
  K : CurveDat d.host d.what₂.embLL d.eTau
  B : Cd.Base (carD d) d.host.ccK K.δ
  χ : Cd.TaylorLogMetric.IdE (carD d) → ℂ

variable {d}

def AmbIn.cD (I : AmbIn d) (τ : d.what₂.Tau) : ℂ := ((I.K.fr τ : I.K.M) : ℂ)

def AmbIn.amb (I : AmbIn d) : Amb d.X := Cd.ambOf (seamD d) I.B I.χ I.cD

def AmbIn.Ok (I : AmbIn d) : Prop := I.B.StdOK ∧ Cd.TaylorLogMetric.IsChi (carD d) I.χ

end OverColDat

end Formalism.L2.Ker
