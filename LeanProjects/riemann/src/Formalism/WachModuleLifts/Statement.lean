import Mathlib

open Finset

noncomputable section

namespace Formalism.CL

variable (p : ℕ) [Fact p.Prime]

def phiPoly : Polynomial ℚ_[p] :=
  Polynomial.X ^ p - Polynomial.C (p : ℚ_[p]) * Polynomial.X ^ (p - 1) + Polynomial.C (p : ℚ_[p])

def phiIter (g : ℕ) : Polynomial ℚ_[p] := (fun f => (phiPoly p).comp f)^[g] Polynomial.X

def uu (g : ℕ) : PowerSeries ℚ_[p] :=
  (p : ℚ_[p])⁻¹ • ((phiIter p g : Polynomial ℚ_[p]) : PowerSeries ℚ_[p])

def Content (g : ℕ) (f : PowerSeries ℚ_[p]) : Prop :=
  ∀ j : ℕ, ‖PowerSeries.coeff j f‖ ≤ (p : ℝ) ^ (j / p ^ g)

def LemmaCPow : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ), 1 ≤ g → ∀ y : ℕ, Content p g (uu p g ^ y)

def LemmaCInv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ), 1 ≤ g →
    (uu p g)⁻¹ * uu p g = 1 ∧ ∀ y : ℕ, Content p g ((uu p g)⁻¹ ^ y)

def ContentMul : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (f f' : PowerSeries ℚ_[p]),
    Content p g f → Content p g f' → Content p g (f * f')

def ContentMono : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g s : ℕ) (f : PowerSeries ℚ_[p]), g ≤ s → Content p s f → Content p g f

def LemmaCSharp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (y r : ℕ), r ≤ y → padicValNat p (y.choose r) < p - 1 →
    ‖PowerSeries.coeff (p * r) (uu p 1 ^ y)‖ = (p : ℝ) ^ ((r : ℤ) - padicValNat p (y.choose r))

def LemmaCSharpInv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (y r : ℕ), 0 < y → padicValNat p ((y + r - 1).choose r) < p - 1 →
    ‖PowerSeries.coeff (p * r) ((uu p 1)⁻¹ ^ y)‖ =
      (p : ℝ) ^ ((r : ℤ) - padicValNat p ((y + r - 1).choose r))

def LemmaCSharpG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ), 1 ≤ g → ∀ (y r : ℕ), r ≤ y →
    padicValNat p (y.choose r) < p - 1 →
    ‖PowerSeries.coeff (p ^ g * r) (uu p g ^ y)‖ = (p : ℝ) ^ ((r : ℤ) - padicValNat p (y.choose r))

def LemmaCSharpGInv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ), 1 ≤ g → ∀ (y r : ℕ), 0 < y →
    padicValNat p ((y + r - 1).choose r) < p - 1 →
    ‖PowerSeries.coeff (p ^ g * r) ((uu p g)⁻¹ ^ y)‖ =
      (p : ℝ) ^ ((r : ℤ) - padicValNat p ((y + r - 1).choose r))

def LemmaCPowMin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ), 1 ≤ g → ∀ (y j : ℕ),
    ‖PowerSeries.coeff j (uu p g ^ y)‖ ≤ (p : ℝ) ^ (min y (j / p ^ g))

def LemmaCSharpOdd1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (y r : ℕ), r ≤ y →
    ‖PowerSeries.coeff (p * r) (uu p 1 ^ y)‖ = (p : ℝ) ^ ((r : ℤ) - padicValNat p (y.choose r))

def LemmaCSharpOdd1Inv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (y r : ℕ), 0 < y →
    ‖PowerSeries.coeff (p * r) ((uu p 1)⁻¹ ^ y)‖ =
      (p : ℝ) ^ ((r : ℤ) - padicValNat p ((y + r - 1).choose r))

def LemmaCSharpOddG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (g : ℕ), 1 ≤ g → ∀ (y r : ℕ), r ≤ y →
    ‖PowerSeries.coeff (p ^ g * r) (uu p g ^ y)‖ = (p : ℝ) ^ ((r : ℤ) - padicValNat p (y.choose r))

def LemmaCSharpOddGInv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (g : ℕ), 1 ≤ g → ∀ (y r : ℕ), 0 < y →
    ‖PowerSeries.coeff (p ^ g * r) ((uu p g)⁻¹ ^ y)‖ =
      (p : ℝ) ^ ((r : ℤ) - padicValNat p ((y + r - 1).choose r))

def phiPS (f : PowerSeries ℚ_[p]) : PowerSeries ℚ_[p] :=
  PowerSeries.mk fun r => ∑ s ∈ range (r + 1),
    PowerSeries.coeff s f *
      ((Polynomial.X + Polynomial.C (p : ℚ_[p])) ^ ((p - 1) * s)).coeff (r - s)

def PhiPSPoly : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : Polynomial ℚ_[p]),
    phiPS p (f : PowerSeries ℚ_[p]) =
      ((f.comp (Polynomial.X * (Polynomial.X + Polynomial.C (p : ℚ_[p])) ^ (p - 1)) :
        Polynomial ℚ_[p]) : PowerSeries ℚ_[p])

def LemmaHStep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : ℝ), 0 ≤ σ → σ ≤ p → ∀ f : PowerSeries ℚ_[p],
    (∀ s : ℕ, ‖PowerSeries.coeff s f‖ ≤ (p : ℝ) ^ (σ * s)) →
    ∀ r : ℕ, ‖PowerSeries.coeff r (phiPS p f)‖ ≤ (p : ℝ) ^ (σ * r / p)

def LemmaHLift : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (V : Type) [NormedAddCommGroup V] [NormedSpace ℚ_[p] V]
    [IsUltrametricDist V] (u : ℚ_[p]) (x : ℕ → V) (c : ℕ → ℕ → V →L[ℚ_[p]] V) (gg : ℕ → V),
    (∀ m : ℕ, 1 ≤ m → ‖u ^ m - 1‖ = (p : ℝ) ^ (-(1 + (padicValNat p m : ℤ)))) →
    (∀ m i, ‖c m i‖ ≤ 1) → (∀ m, ‖gg m‖ ≤ 1) → ‖x 0‖ ≤ 1 →
    (∀ m : ℕ, 1 ≤ m → (u ^ m - 1) • x m = (∑ i ∈ range m, c m i (x i)) + gg m) →
    ∀ m : ℕ, ‖x m‖ ≤ (p : ℝ) ^ (m + padicValNat p m.factorial)

def Legendre : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m : ℕ),
    ((m : ℝ) + padicValNat p m.factorial) ≤ (m : ℝ) * p / (p - 1)

def Interp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (a : Fin n → ℤ_[p]) (Q : Polynomial ℤ_[p]) (e : ℕ),
    Function.Injective a →
    (∀ i : Fin n, ‖(p : ℤ_[p]) ^ e‖ ≤ ‖Q.eval (a i) * ∏ k ∈ univ.erase i, (a i - a k)‖) →
    Polynomial.C ((p : ℤ_[p]) ^ e) ∈
      Ideal.span ({∏ i : Fin n, (Polynomial.X - Polynomial.C (a i)), Q} : Set (Polynomial ℤ_[p]))

def LTE : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ u : ℤ_[p], ‖u - 1‖ = (p : ℝ)⁻¹ → ∀ m : ℕ, 1 ≤ m →
    ‖u ^ m - 1‖ = (p : ℝ) ^ (-(1 + (padicValNat p m : ℤ)))

def TwoPoly : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ u : ℤ_[p]ˣ, ‖(u : ℤ_[p]) - 1‖ = (p : ℝ)⁻¹ →
    ∀ A : ℕ, 1 ≤ A →
    Polynomial.C ((p : ℤ_[p]) ^ (2 * A - 1 + (2 * A - 1) / (p - 1))) ∈
      Ideal.span ({∏ i ∈ range A, (Polynomial.X - Polynomial.C ((u : ℤ_[p]) ^ i)),
                   ∏ j ∈ Icc 1 A, (Polynomial.X - Polynomial.C (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ^ j))} :
        Set (Polynomial ℤ_[p]))

def RdLemma : Prop :=
  ∀ (R : Type) [CommRing R] (Z : Type) [AddCommGroup Z] [Module R Z] [NoZeroSMulDivisors R Z]
    (d : Module.End R Z) (Rp : Polynomial R) (c : R) (w w' : Z),
    Polynomial.aeval d (Polynomial.X * Rp) = 0 → c ≠ 0 → c • w = d w' →
    Rp.eval 0 • w ∈ LinearMap.range d

def LiftChase : Prop :=
  ∀ (R : Type) [CommRing R]
    (K01 K02 LastRowCutoff PoissonCutoffFormula K21 K22 : Type)
    [AddCommGroup K01] [Module R K01] [AddCommGroup K02] [Module R K02]
    [AddCommGroup LastRowCutoff] [Module R LastRowCutoff] [AddCommGroup PoissonCutoffFormula] [Module R PoissonCutoffFormula]
    [AddCommGroup K21] [Module R K21] [AddCommGroup K22] [Module R K22]
    (d0 : K01 →ₗ[R] K02) (d1 : LastRowCutoff →ₗ[R] PoissonCutoffFormula) (d2 : K21 →ₗ[R] K22)
    (ι1 : K01 →ₗ[R] LastRowCutoff) (ι2 : K02 →ₗ[R] PoissonCutoffFormula) (π1 : LastRowCutoff →ₗ[R] K21) (π2 : PoissonCutoffFormula →ₗ[R] K22),
    (∀ x, d1 (ι1 x) = ι2 (d0 x)) → (∀ x, d2 (π1 x) = π2 (d1 x)) → (∀ x, π1 (ι1 x) = 0) →
    Function.Surjective π1 → Function.Injective ι2 → LinearMap.ker π2 = LinearMap.range ι2 →
    ∀ (c : R) (y₂ : K21), d2 y₂ = 0 →
      (∀ (y₁ : LastRowCutoff) (ω : K02), π1 y₁ = y₂ → ι2 ω = d1 y₁ → c • ω ∈ LinearMap.range d0) →
      ∃ x : LastRowCutoff, d1 x = 0 ∧ π1 x = c • y₂

def EqBelow (B : ℕ) (f h : PowerSeries ℚ_[p]) : Prop :=
  ∀ j < B, PowerSeries.coeff j f = PowerSeries.coeff j h

def IntBelow (B : ℕ) (f : PowerSeries ℚ_[p]) : Prop := ∀ j < B, ‖PowerSeries.coeff j f‖ ≤ 1

def ExactContent (B : ℕ) (f : PowerSeries ℚ_[p]) (β : ℤ) : Prop :=
  (∀ j < B, ‖PowerSeries.coeff j f‖ ≤ (p : ℝ) ^ β) ∧ ∃ j < B, ‖PowerSeries.coeff j f‖ = (p : ℝ) ^ β

def DirUD : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (B : ℕ) (w w' a g : PowerSeries ℚ_[p]) (β t s : ℤ),
    w * w' = 1 → ExactContent p B w β → IntBelow p B a → IntBelow p B g → 0 < s →
    EqBelow p B (PowerSeries.C ((p : ℚ_[p]) ^ (-s)))
      (a + PowerSeries.C ((p : ℚ_[p]) ^ t) * w' * g) →
    s ≤ -t - β

def DirDD : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (B : ℕ) (w w' a g : PowerSeries ℚ_[p]) (β t s m : ℤ),
    w * w' = 1 → ExactContent p B w' β → IntBelow p B a → IntBelow p B g → s < m →
    EqBelow p B (PowerSeries.C ((p : ℚ_[p]) ^ s))
      (PowerSeries.C ((p : ℚ_[p]) ^ m) * a + PowerSeries.C ((p : ℚ_[p]) ^ t) * w * g) →
    t + β ≤ s

end Formalism.CL
