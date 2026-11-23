import Mathlib
import Formalism.PieriBlockIdeals.PieriColumnMinors.RowGenDerivative

open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section

namespace GlobalTheory.LeviCut

def GlRel (N : ℕ) {A : Type} [Ring A] (e : ℕ → ℕ → A) : Prop :=
  ∀ a b c d : ℕ, a < N → b < N → c < N → d < N →
    e a b * e c d - e c d * e a b = (if b = c then e a d else 0) - (if d = a then e c b else 0)

def coef (j k : ℕ) : ℚ := (-1) ^ k * (j.factorial : ℚ) / ((k.factorial : ℚ) * ((k + j + 1).factorial : ℚ))

def proj {A : Type} [Ring A] [Algebra ℚ A] (K j : ℕ) (X Y : A) : A :=
  ∑ k ∈ Finset.range (K + 1), coef j k • (Y ^ k * X ^ k)

def rootP {A : Type} [Ring A] [Algebra ℚ A] (D : ℕ → ℕ → A) (K i j : ℕ) : A :=
  proj K (j - i - 1) (D i j) (D j i)

def rowP {A : Type} [Ring A] [Algebra ℚ A] (D : ℕ → ℕ → A) (K i s n : ℕ) : A :=
  ((List.range' s n).map (rootP D K i)).prod

def gridP {A : Type} [Ring A] [Algebra ℚ A] (D : ℕ → ℕ → A) (K a b t : ℕ) : A :=
  ((List.range t).reverse.map fun i => rowP D K i a b).prod

def adj {A : Type} [Ring A] [Algebra ℚ A] (x : A) : Module.End ℚ A :=
  LinearMap.mulLeft ℚ x - LinearMap.mulRight ℚ x

def IsWt (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) (μ : ℕ → ℤ) (x : V) : Prop :=
  ∀ c < N, e c c x = (μ c : ℚ) • x

def Bdd (N K : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) : Prop :=
  ∀ a < N, ∀ b < N, ∀ (n : ℤ) (x : V), e a a x - e b b x = (n : ℚ) • x → (K : ℤ) < n → x = 0

def Dom (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) (lam : ℕ → ℤ) : Prop :=
  ∀ (μ : ℕ → ℤ) (x : V), IsWt N e μ x → x ≠ 0 →
    (∀ k ≤ N, ∑ c ∈ Finset.range k, μ c ≤ ∑ c ∈ Finset.range k, lam c) ∧
      ∑ c ∈ Finset.range N, μ c = ∑ c ∈ Finset.range N, lam c

def WtSpan (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) : Prop :=
  Submodule.span ℚ {x : V | ∃ μ : ℕ → ℤ, IsWt N e μ x} = ⊤

def DivStable (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V)
    (L : Submodule ℤ V) : Prop :=
  ∀ i < N, ∀ j < N, i ≠ j → ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (e i j ^ k) x ∈ L

def RankOne : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (N K : ℕ) (D : ℕ → ℕ → Module.End ℚ W), GlRel N D → Bdd N (2 * K) D →
    ∀ o q : ℕ, o < N → q < N → o ≠ q → ∀ T : W, D o o T = 0 → D q q T = 0 →
      D o q (proj K 0 (D o q) (D q o) T) = 0 ∧ (D o q T = 0 → D q o T = 0)

def RankTwo : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (N K : ℕ) (D : ℕ → ℕ → Module.End ℚ W), GlRel N D → Bdd N (2 * K) D →
    ∀ o p q : ℕ, o < N → p < N → q < N → o ≠ p → o ≠ q → p ≠ q → ∀ (j : ℕ) (T : W),
      D o o T = 0 → D p p T = 0 → D q q T = 0 → D p q T = 0 →
      D p q (proj K j (D o p) (D p o) (proj K (j + 1) (D o q) (D q o) T)) = 0

def GridInv : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (a b K : ℕ) (D : ℕ → ℕ → Module.End ℚ W), GlRel (a + b) D →
    Bdd (a + b) (2 * K) D → ∀ T : W, (∀ c < a + b, ∀ d < a + b, (c < a ↔ d < a) → D c d T = 0) →
      ∀ c < a + b, ∀ d < a + b, D c d (gridP D K a b a T) = 0

def AdjBdd : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (N K : ℕ) (e : ℕ → ℕ → Module.End ℚ V), GlRel N e → Bdd N K e →
    WtSpan N e → GlRel N (fun a b => adj (e a b)) ∧ Bdd N (2 * K) (fun a b => adj (e a b))

def StepScalar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (E F H T : Module.End ℚ V) (v : V) (φ : V →ₗ[ℚ] ℚ) (n K j : ℕ),
    E * F - F * E = H → H * F - F * H = -(F + F) → E v = 0 → H v = (n : ℚ) • v → n ≤ K → (∀ x, φ (F x) = 0) →
    (∀ k : ℕ, 0 < k → T ((F ^ k) v) = 0) →
      φ (proj K j (adj E) (adj F) T v) * ((n : ℚ) + j + 1) = φ (T v)

def GridScalar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (a b K : ℕ) (e : ℕ → ℕ → Module.End ℚ V) (lam : ℕ → ℤ) (v : V)
    (φ : V →ₗ[ℚ] ℚ) (T : Module.End ℚ V), GlRel (a + b) e → Dom (a + b) e lam → IsWt (a + b) e lam v →
    (∀ i j : ℕ, i < j → j < a + b → e i j v = 0 ∧ (∀ x, φ (e j i x) = 0) ∧ lam j ≤ lam i ∧ lam i ≤ lam j + K) →
    (∀ (μ : ℕ → ℤ) (x : V), IsWt (a + b) e μ x → ∑ c ∈ Finset.range a, μ c < ∑ c ∈ Finset.range a, lam c → T x = 0) →
      φ (gridP (fun c d => adj (e c d)) K a b a T v) *
        ((∏ i ∈ Finset.range a, ∏ j ∈ Finset.Ico a (a + b), (lam i - lam j + (j : ℤ) - (i : ℤ)) : ℤ) : ℚ) = φ (T v)

def GridInt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (a b K w Λ : ℕ) (e : ℕ → ℕ → Module.End ℚ V) (L M : Submodule ℤ V),
    DivStable (a + b) e L → DivStable (a + b) e M → K + (a + b) ≤ w + 1 →
    (∀ j k : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ Λ * (j.factorial * k.factorial)) →
    ∀ (c : ℕ) (T : Module.End ℚ V), (∀ x ∈ L, (c : ℤ) • T x ∈ M) →
      ∀ x ∈ L, ((c * Λ ^ (a * b) : ℕ) : ℤ) • gridP (fun c d => adj (e c d)) K a b a T x ∈ M

def BetaDen : Prop :=
  ∀ l w : ℕ, l.Prime → ∃ m : ℕ, ¬ l ∣ m ∧
    ∀ j k : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ (m * l ^ Nat.log l w) * (j.factorial * k.factorial)

def eV (N : ℕ) (ν : Fin N → ℕ) (a b : ℕ) : Module.End ℚ (dualWeyl ℚ N N ν) :=
  if h : a < N ∧ b < N then
    LinearMap.restrict (Formalism.CohomologicalDescent.LR.der N N ⟨a, h.1⟩ ⟨b, h.2⟩ : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ))
      (fun f hf => Formalism.CohomologicalDescent.LR.der_mem ν _ _ f hf)
  else 0

def latV (N : ℕ) (ν : Fin N → ℕ) (M : Submodule ℤ (MvPolynomial (Fin N × Fin N) ℤ)) : Submodule ℤ (dualWeyl ℚ N N ν) :=
  (M.map (intQ N N)).comap ((dualWeyl ℚ N N ν).subtype.restrictScalars ℤ)

def wtZ {N : ℕ} (ν : Fin N → ℕ) (c : ℕ) : ℤ := if h : c < N then (ν ⟨c, h⟩ : ℤ) else 0

def resVarT (R : Type) [CommRing R] (p q : ℕ) (v : Fin (p + q) × Fin (p + q)) :
    MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R :=
  Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R)
    (fun a => Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R)
      (fun s => X (a, s) ⊗ₜ[R] 1) (fun _ => 0) v.2)
    (fun b => Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R)
      (fun _ => 0) (fun t => 1 ⊗ₜ[R] X (b, t)) v.2) v.1

def resT (R : Type) [CommRing R] (p q : ℕ) : MvPolynomial (Fin (p + q) × Fin (p + q)) R →ₐ[R]
    MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R :=
  aeval (resVarT R p q)

def NablaGl : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
    GlRel N (eV N ν) ∧ WtSpan N (eV N ν) ∧ Dom N (eV N ν) (wtZ ν) ∧
      DivStable N (eV N ν) (latV N ν (dualWeyl ℤ N N ν)) ∧ DivStable N (eV N ν) (latV N ν (weyl ℤ N N le_rfl ν))

def NablaBdd : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ K : ℕ, (∀ i j, ν i ≤ ν j + K) → Bdd N K (eV N ν)

def NablaSchur : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) (S : Module.End ℚ (dualWeyl ℚ N N ν)),
    (∀ c < N, ∀ d < N, eV N ν c d * S = S * eV N ν c d) →
    fockQ (hw ℚ le_rfl ν) (S ⟨hw ℚ le_rfl ν, hwMem ℚ N N le_rfl ν hν⟩ : dualWeyl ℚ N N ν) =
      fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) → S = 1

def SubstMem : Prop :=
  ∀ (R : Type) [CommRing R] (k N : ℕ) (τ : Fin k → Fin N), StrictMono τ →
    ∀ ψ : Fin N × Fin N → MvPolynomial (Fin k × Fin k) R,
      (∀ a s, ψ (τ a, τ s) = X (a, s)) → (∀ x s, x ∉ Set.range τ → ψ (x, τ s) = 0) →
      (∀ x y, y ∉ Set.range τ → ∃ c : R, ψ (x, y) = C c) →
      ∀ (ν : Fin N → ℕ), ∀ f ∈ dualWeyl R N N ν, aeval ψ f ∈ dualWeyl R k k (fun s => ν (τ s))

def ResLat : Prop :=
  ∀ (p q : ℕ) (ν : Fin (p + q) → ℕ), ∀ f ∈ dualWeyl ℤ (p + q) (p + q) ν,
    resT ℚ p q (intQ (p + q) (p + q) f) ∈ Submodule.span ℤ
      {z | ∃ f₁ ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)), ∃ f₂ ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)),
        z = intQ p p f₁ ⊗ₜ[ℚ] intQ q q f₂}

def ResHw : Prop :=
  ∀ (p q : ℕ) (ν : Fin (p + q) → ℕ), Antitone ν →
    resT ℚ p q (hw ℚ le_rfl ν) =
      hw ℚ le_rfl (fun i => ν (Fin.castAdd q i)) ⊗ₜ[ℚ] hw ℚ le_rfl (fun j => ν (Fin.natAdd p j))

def ResDer : Prop :=
  ∀ (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ),
    (∀ c d : Fin p, resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q d) f) =
      LinearMap.rTensor _ (Formalism.CohomologicalDescent.LR.der p p c d : Module.End ℚ (MvPolynomial (Fin p × Fin p) ℚ)) (resT ℚ p q f)) ∧
    (∀ c d : Fin q, resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.natAdd p c) (Fin.natAdd p d) f) =
      LinearMap.lTensor _ (Formalism.CohomologicalDescent.LR.der q q c d : Module.End ℚ (MvPolynomial (Fin q × Fin q) ℚ)) (resT ℚ p q f)) ∧
    ∀ (ν : Fin (p + q) → ℕ) (t : ℚ), IsWeightedHomogeneous (colW (p + q) (p + q)) f ν →
      ∑ c : Fin p, Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q c) f = t • f →
      t ≠ ∑ c : Fin p, (ν (Fin.castAdd q c) : ℚ) → resT ℚ p q f = 0

def LeviProj : Prop :=
  ∀ (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) (c₁ c₂ : ℕ),
    (∀ x ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)), (c₁ : ℤ) • x ∈ weyl ℤ p p le_rfl (fun i => ν (Fin.castAdd q i))) →
    (∀ x ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)), (c₂ : ℤ) • x ∈ weyl ℤ q q le_rfl (fun j => ν (Fin.natAdd p j))) →
    ∃ T : Module.End ℚ (dualWeyl ℚ (p + q) (p + q) ν),
      (∀ c < p + q, ∀ d < p + q, (c < p ↔ d < p) → eV (p + q) ν c d * T = T * eV (p + q) ν c d) ∧
      (∀ x ∈ latV (p + q) ν (dualWeyl ℤ (p + q) (p + q) ν),
        ((c₁ * c₂ : ℕ) : ℤ) • T x ∈ latV (p + q) ν (weyl ℤ (p + q) (p + q) le_rfl ν)) ∧
      (∀ (μ : ℕ → ℤ) (x : dualWeyl ℚ (p + q) (p + q) ν), IsWt (p + q) (eV (p + q) ν) μ x →
        ∑ c ∈ Finset.range p, μ c < ∑ c ∈ Finset.range p, wtZ ν c → T x = 0) ∧
      fockQ (hw ℚ le_rfl ν) (T ⟨hw ℚ le_rfl ν, hwMem ℚ (p + q) (p + q) le_rfl ν hν⟩ : dualWeyl ℚ (p + q) (p + q) ν) =
        fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)

end GlobalTheory.LeviCut
