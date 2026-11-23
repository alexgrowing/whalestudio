import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

def NonsingNorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K), IntCurve W →
    ∀ x y : K, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → W.toAffine.Equation x y →
      ‖2 * y + W.a₁ * x + W.a₃‖ = 1 ∨ ‖3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y‖ = 1

def UnitKap : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ P : W.toAffine.Point, P ≠ 0 → P + P = 0 → ‖px W P‖ ≤ 1 → ‖py W P‖ ≤ 1 →
      psi2 W P = 0 ∧ ‖kapP W P‖ = 1

def UnitPsi2 : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ P : W.toAffine.Point, P ≠ 0 → P + P ≠ 0 → ‖px W P‖ ≤ 1 → ‖py W P‖ ≤ 1 →
      ‖px W (P + P)‖ ≤ 1 → ‖psi2 W P‖ = 1

def UnitDiff : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ P Q : W.toAffine.Point, P ≠ 0 → Q ≠ 0 → P + Q ≠ 0 → P - Q ≠ 0 →
      ‖px W P‖ ≤ 1 → ‖py W P‖ ≤ 1 → ‖px W Q‖ ≤ 1 → ‖py W Q‖ ≤ 1 →
      ‖px W (P + Q)‖ ≤ 1 → ‖px W (P - Q)‖ ≤ 1 → ‖px W P - px W Q‖ = 1

def IntRules : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K],
    (∀ a : K, ‖a‖ ≤ 1 → IntS (C a)) ∧ IntS (X : K⟦X⟧) ∧
    (∀ f g : K⟦X⟧, IntS f → IntS g → IntS (f + g)) ∧ (∀ f : K⟦X⟧, IntS f → IntS (-f)) ∧
    (∀ f g : K⟦X⟧, IntS f → IntS g → IntS (f * g)) ∧ (∀ (f : K⟦X⟧) (n : ℕ), IntS f → IntS (f ^ n)) ∧
    (∀ f g : K⟦X⟧, OneUnit f → OneUnit g → OneUnit (f * g)) ∧
    (∀ (f : K⟦X⟧) (n : ℕ), OneUnit f → OneUnit (f ^ n)) ∧
    (∀ f g : K⟦X⟧, OneUnit f → f * g = 1 → OneUnit g) ∧
    (∀ f : K⟦X⟧, IntS f ↔ Formalism.DworkPowerSeriesWeights.Integral (ι := Unit) f)

def UnitAtRules : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K],
    (∀ (j k : ℕ) (f g : K⟦X⟧), UnitAt j f → UnitAt k g → UnitAt (j + k) (f * g)) ∧
    (∀ (k n : ℕ) (f : K⟦X⟧), UnitAt k f → UnitAt (k * n) (f ^ n)) ∧
    (∀ (k : ℕ) (f : K⟦X⟧), IntS f → (∀ i, i < k → coeff i f = 0) → ‖coeff k f‖ = 1 → UnitAt k f) ∧
    (∀ (k : ℕ) (f : K⟦X⟧), UnitAt k f → GaussOne f) ∧
    (∀ (k : ℕ) (f : K⟦X⟧) (a : K), ‖a‖ = 1 → UnitAt k f → UnitAt k (C a * f))

def RootInt : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (N : ℕ) (g : K⟦X⟧), ‖(N : K)‖ = 1 →
    constantCoeff g = 1 → IntS (g ^ N) → IntS g

def GaussMul : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (f g : K⟦X⟧),
    GaussOne f → GaussOne g → GaussOne (f * g)

end Formalism.L2.Th1.E
