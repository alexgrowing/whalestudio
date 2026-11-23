import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndRefine

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma
open Formalism.HermitianLatticeCounting.S7 (P0 b1 Ydat)

def cnd_CovLe (Nmax : ℕ) (κ : ℝ) (P : ℝ → Prop) : Prop :=
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℝ V) (_ : FiniteDimensional ℝ V) (M : Submodule ℤ V),
    DiscreteTopology M ∧ Submodule.span ℝ (M : Set V) = ⊤ ∧ Module.finrank ℝ V ≤ Nmax ∧
    (∀ y ∈ Formalism.HadamardInequality.zdual M, y ≠ 0 → κ ≤ ‖y‖) ∧ ∀ R : ℝ, (∀ x : V, ∃ y ∈ M, ‖x - y‖ ≤ R) → P R

def cnd_Diam (X : CData) (Cq ρ ρ₀ : ℝ) : Prop :=
  cnd_CovLe (2 * X.I.n ^ 2 * X.I.f) (Real.sqrt (X.I.f : ℝ) / (2 * X.I.rd * ρ₀)) fun R₁ =>
    cnd_CovLe (2 * X.I.n ^ 2 * X.I.f) (Real.sqrt (X.I.f : ℝ) / (2 * X.I.rd * ρ₀)) fun R₂ =>
      ρ ≤ Cq * Real.sqrt (X.I.f : ℝ) * (X.g : ℝ) * (R₁ + R₂)

def CSize.DeepStepsQ {X : CData} (S : CSize X) (volK C Cq : ℝ) : Prop :=
  0 < volK ∧ X.I.vol X.μf X.fund / volK ≤ cn_Y X ^ (C * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) ∧
    ∀ᵐ x ∂X.μ, S.tau1 x < 1 / 2 →
      ∃ (a : ℕ) (τ : ℕ → ℝ), 1 ≤ a ∧ a ≤ X.qq ∧ (∀ i, 0 < τ i) ∧ τ (a + 1) = 1 / 2 ∧ τ 1 = S.tau1 x ∧
        ∀ b' : ℕ, 1 ≤ b' → b' ≤ a → ∃ (ρ : ℝ) (s : ℕ → ℝ) (mult : ℝ), 0 ≤ ρ ∧
          cnd_Diam X Cq ρ (τ b' / τ (b' + 1)) ∧ (∀ P, 0 ≤ s P) ∧
          |(X.kerD x).re| ≤ s 0 ^ 2 ∧
          (∀ P < P0 X.I.n X.qq X.I.f, s P ≤ ρ * Real.sqrt ((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) *
            (C * (X.I.n : ℝ) * (X.b ^ 2 + (P : ℝ) * (X.I.n : ℝ))) * s (P + 1)) ∧
          s (P0 X.I.n X.qq X.I.f) ^ 2 ≤ (4 / (1 / (C * (X.I.n : ℝ) * b1 X.I.n X.qq X.I.f X.b))) ^ (X.I.n ^ 2 * X.I.f) * mult *
            (X.Dc / volK) ∧
          mult ≤ (C * Real.sqrt (X.I.n : ℝ) / S.tau1 x ^ 2) ^ (2 * X.I.n ^ 2 * X.I.f)

end Formalism.MainNotions.LeviCoordinates

end
