import Formalism.PadicSubsetSums.CentralIdempotents.WindowSums

noncomputable section

namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial

def SqrtNegInCyclotomic : Prop :=
  ∀ (l : ℕ), l.Prime → l % 4 = 3 → ∀ (F : Type) [Field F] (ζ : F), IsPrimitiveRoot ζ l →
    IsSquare (-(l : F))

def DictRing : Prop :=
  ∀ (A₁ G : Type) [CommRing A₁] [Group G] [Fintype G] [MulSemiringAction G A₁]
    (p q E w u : A₁) (φ γ : A₁ →+* A₁) (vv : G → A₁ˣ) (ε₀ : A₁ˣ),
    (∀ x y : A₁, p * x = p * y → x = y) →
    (∀ g : G, g • p = p * vv g) → φ p = p * q → q = ε₀ * E → γ p = p * w →
    (∀ (g : G) (x : A₁), φ (g • x) = g • φ x) → (∀ (g : G) (x : A₁), γ (g • x) = g • γ x) →
    (∀ g : G, g • u = u) → p ∣ w - u → (∀ x : A₁, p ∣ γ x - x) →
    (∀ x : A₁, (∀ g : G, g • x = x) → p ∣ x → (∏ g : G, g • p) ∣ x) →
    (∃ ε : A₁ˣ, (∏ g : G, g • p) = ε * p ^ Fintype.card G) ∧
    (∃ ε : A₁ˣ, φ (∏ g : G, g • p) = ε * (∏ g : G, g • p) * E ^ Fintype.card G) ∧
    ((∏ g : G, g • p) ^ 2 ∣ γ (∏ g : G, g • p) - u ^ Fintype.card G * (∏ g : G, g • p)) ∧
    (∀ (y : ℕ) (f : A₁), (∀ g : G, g • f = f) →
      (∏ g : G, g • p) ^ (y + 1) ∣
        γ ((∏ g : G, g • p) ^ y * f) - u ^ (Fintype.card G * y) * ((∏ g : G, g • p) ^ y * f))

def PhiFiltrationMem : Prop :=
  ∀ (l e s H a : ℕ), l.Prime → e * s = l - 1 → a = ⌈((e * H : ℕ) : ℝ) / ((l : ℝ) - 1)⌉₊ →
    ¬ l ∣ s ∧ H ≤ s * a

def HorizInj : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (γ ϖ : Module.End R V) (c : ℕ → R),
    Function.Injective ϖ →
    (∀ (i : ℕ) (x : V), ∃ y, γ ((ϖ ^ i) x) - c i • (ϖ ^ i) x = (ϖ ^ (i + 1)) y) →
    (∀ (i : ℕ), 1 ≤ i → ∀ x y : V, (c i - 1) • x = ϖ y → ∃ x', x = ϖ x') →
    ∀ (k : ℕ) (w r : V), γ (ϖ w) - ϖ w = (ϖ ^ k) r → ∃ r', ϖ w = (ϖ ^ k) r'

def LogShift : Prop :=
  ∀ (l h S : ℕ), 2 ≤ l → 1 ≤ h → Real.logb l ((h : ℝ) + S) ≤ Real.logb l h + S

def BracketA : Prop :=
  ∀ (l e h S η n r m e' : ℕ) (c ρ σ κ y : ℝ), 3 ≤ l → 1 ≤ e → 1 ≤ h → 0 ≤ c →
    ρ ≤ 9 * ((e * h : ℕ) : ℝ) / l + 3 → σ ≤ 9 * ((e * h : ℕ) : ℝ) / l + 3 →
    κ ≤ (e : ℝ) * ((S : ℝ) + (S : ℝ) / ((l : ℝ) - 1) + Real.logb l ((h : ℝ) + S)) →
    y ≤ c * (ρ + σ) + κ + η + 1 + Real.logb l h →
    y ≤ (18 * c + 3) *
      (((e * h : ℕ) : ℝ) / l + (e : ℝ) * S + (e : ℝ) * Real.logb l h + 1 + η) ∧
    ((n : ℝ) * e + 1) * r * y + (n : ℝ) * e * ((e : ℝ) + 1) * m * e' ≤
      (18 * c + 3) * (((n : ℝ) * e + 1) * r *
        (((e * h : ℕ) : ℝ) / l + (e : ℝ) * S + (e : ℝ) * Real.logb l h + 1 + η)) +
      (n : ℝ) * e * ((e : ℝ) + 1) * m * e'

def PDPowFrob : Prop :=
  (∀ (l i : ℕ), l.Prime → 1 ≤ i → (i.factorial ^ l * l) ∣ (l * i).factorial) ∧
  ∀ (l i : ℕ), l.Prime → 1 ≤ i → ∀ (A : Type) [CommRing A] [Algebra ℚ A] (S : Subring A) (x : A),
    (∀ k : ℕ, algebraMap ℚ A (1 / (k.factorial : ℚ)) * x ^ k ∈ S) →
    ∃ z ∈ S, (algebraMap ℚ A (1 / (i.factorial : ℚ)) * x ^ i) ^ l = (l : A) * z

def FrobDiffPD : Prop :=
  ∀ (l : ℕ), l.Prime → ∀ (A : Type) [CommRing A] [Algebra ℚ A] (S : Subring A) (u x : A),
    u ∈ S → x ∈ S → algebraMap ℚ A (1 / (l.factorial : ℚ)) * x ^ l ∈ S →
    ∃ Y ∈ S, (u + x) ^ l - u ^ l = (l : A) * Y

def FallingWeyl : Prop :=
  ∀ (B : Type) [Ring B] (u D : B), D * u = u * D + 1 →
    ∀ i : ℕ, u ^ i * D ^ i = aeval (u * D) (descPochhammer ℤ i)

def FallingN : Prop :=
  ∀ (R : Type) [CommRing R] (i : ℕ) (f : R[X]),
    aeval ((LinearMap.mulLeft R (X : R[X])) ∘ₗ (derivative : R[X] →ₗ[R] R[X]) : Module.End R R[X])
      (descPochhammer R i) f = X ^ i * (derivative^[i] f)

def EulerCoord : Prop :=
  ∀ (K : Type) [Field K] (l : K), l ≠ 0 → ∃ ω : (PowerSeries K)ˣ,
    (PowerSeries.X * (ω : PowerSeries K)) * (PowerSeries.C l - PowerSeries.X) =
      PowerSeries.C l * PowerSeries.X ∧
    ∀ j : ℕ, PowerSeries.X * (PowerSeries.X - PowerSeries.C l) *
        PowerSeries.derivative K ((PowerSeries.X * (ω : PowerSeries K)) ^ j) =
      -(PowerSeries.C l * (j : PowerSeries K)) * (PowerSeries.X * (ω : PowerSeries K)) ^ j

def CokerT : Prop :=
  ∀ (R V Vb : Type) [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup Vb] [Module R Vb]
    (𝓋 : Module.End R V) (pr : V →ₗ[R] Vb) (N : Module.End R Vb) (V' : Submodule R V)
    (P₁ P₂ : R[X]) (d : R) (A' l : ℕ),
    Function.Injective 𝓋 → Function.Surjective pr → LinearMap.ker pr = LinearMap.range (𝓋 ^ l) →
    2 * A' ≤ l → (∀ x ∈ V', 𝓋 x ∈ V') → (∀ x, (𝓋 ^ A') x ∈ V') →
    (∀ z ∈ (V'.map (𝓋 ^ A')).map pr, N z ∈ (V'.map (𝓋 ^ A')).map pr) →
    (∀ x ∈ V', aeval N P₁ (pr x) ∈ (V'.map (𝓋 ^ A')).map pr) →
    (∀ x, aeval N P₂ (pr ((𝓋 ^ A') x)) ∈ (LinearMap.range (𝓋 ^ (2 * A'))).map pr) →
    C d ∈ Ideal.span ({P₁, P₂} : Set R[X]) →
    ∀ x : V, d • x ∈ V'

def PDBinom : Prop :=
  (∀ (A : Type) [CommRing A] [Algebra ℚ A] (E p : A) (m : ℕ),
    (E - p) ^ m = (m.factorial : A) * ∑ i ∈ Finset.range (m + 1),
      (algebraMap ℚ A (1 / (i.factorial : ℚ)) * E ^ i) *
        (algebraMap ℚ A (1 / ((m - i).factorial : ℚ)) * (-p) ^ (m - i))) ∧
  ∀ (l k : ℕ), l.Prime → padicValNat l k.factorial ≤ k

def PDPowerMem : Prop :=
  ∀ (l : ℕ), l.Prime → ∀ (A : Type) [CommRing A] [Algebra ℚ A] (S : Subring A) (E : A),
    (∀ i : ℕ, algebraMap ℚ A (1 / (i.factorial : ℚ)) * E ^ i ∈ S) →
    (∀ a : ℚ, 0 ≤ padicValRat l a → algebraMap ℚ A a ∈ S) →
    ∀ m : ℕ, ∃ z ∈ S, (E - (l : A)) ^ m = (m.factorial : A) * z

def PhiFilExp : Prop :=
  (∀ (l j i : ℕ), l.Prime → j + 1 ≤ l → j ≤ i → j + padicValNat l i.factorial ≤ i) ∧
  ∀ (l i : ℕ), l.Prime → 1 ≤ i → 1 + padicValNat l i.factorial ≤ i

def PhiFilMem : Prop :=
  ∀ (l : ℕ), l.Prime → ∀ (A : Type) [CommRing A] [Algebra ℚ A] (S : Subring A) (c : A), c ∈ S →
    (∀ a : ℚ, 0 ≤ padicValRat l a → algebraMap ℚ A a ∈ S) →
    ∀ j i : ℕ, j + 1 ≤ l → j ≤ i →
      ∃ z ∈ S, algebraMap ℚ A (1 / (i.factorial : ℚ)) * ((l : A) * c) ^ i = (l : A) ^ j * z

def TailGlue : Prop :=
  (∀ (l H η : ℕ), η < H → (l : ℤ) - 14 * H ≤ (l : ℤ) - 10 * H - (H + η + 1) - η) ∧
  (∀ (l e c r' n : ℕ), 1 ≤ l → e ≤ c * (l ^ r' - 1) → r' ≤ n → e * l ^ (n - r') ≤ c * l ^ n) ∧
  ∀ (l i n : ℕ), 2 ≤ l → 2 ≤ i → 1 ≤ n → i ≤ (i - 1) * l ^ n

end Formalism.IrreducibleCountingLemmas.WindowSums
