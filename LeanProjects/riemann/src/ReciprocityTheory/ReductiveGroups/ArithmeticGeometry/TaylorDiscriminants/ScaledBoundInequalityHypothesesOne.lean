import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.TB

open ComplexConjugate

noncomputable def netForm {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι]
    (ev : ι → V →ₗ[ℂ] ℂ) (F G : V) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * ∑ y, ev y F * conj (ev y G)

def NetHermSt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) [Fintype ι] (ev : ι → V →ₗ[ℂ] ℂ),
    (∀ F G, netForm ev G F = conj (netForm ev F G)) ∧
    (∀ F, (netForm ev F F).im = 0 ∧ 0 ≤ (netForm ev F F).re) ∧
    ((∀ F, (∀ y, ev y F = 0) → F = 0) → ∀ F, netForm ev F F = 0 → F = 0)

def NetSupSt : Prop :=
  ∀ (ι : Type) [Fintype ι] (f : ι → ℝ) (S : ℝ), (∀ y, 0 ≤ f y) → 0 ≤ S → (∃ y, S / 4 ≤ f y) →
    S ≤ 4 * Real.sqrt (Fintype.card ι) * Real.sqrt ((Fintype.card ι : ℝ)⁻¹ * ∑ y, f y ^ 2)

def SchwarzBallSt : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (u : E → ℂ) (ρ M : ℝ),
    0 < ρ → DifferentiableOn ℂ u (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : E) ρ, ‖u z - u 0‖ ≤ M) →
      ∀ z ∈ Metric.ball (0 : E) ρ, ‖u z - u 0‖ ≤ M * ‖z‖ / ρ

def EBasisSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    [Module ℚ W] [IsScalarTower ℚ E W] (ι : Type) [Fintype ι] (v : ι → W),
    LinearIndependent ℚ v → Fintype.card ι = Module.finrank ℚ E * Module.finrank E W →
      ∃ s : Finset ι, s.card = Module.finrank E W ∧ LinearIndependent E (fun i : s => v i) ∧
        Submodule.span E (Set.range fun i : s => v i) = ⊤

def ScaledBoundInequality : Prop :=
  ∀ (P lNc D L G2 G1 : ℝ), 0 ≤ P → 0 ≤ lNc → 1 ≤ D → 1 ≤ L → G2 ≤ (D + 4) * L → G1 ≤ 2 * L →
    2 * lNc + P * G2 ≤ (5 * P + 2 * lNc / D) * D * L ∧
      2 * lNc + P * G1 ≤ 2 * ((5 * P + 2 * lNc / D) * D * L)

end ReciprocityTheory.ChartRestriction.G.TB
