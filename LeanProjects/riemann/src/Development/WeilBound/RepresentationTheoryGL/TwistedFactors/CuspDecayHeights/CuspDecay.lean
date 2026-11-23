import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe

noncomputable section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace

namespace PositivityTheory.Rg.Tf.Core

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def PolyBd (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n) : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, ∀ (φ : L2 μ) (x : G1 K n), ‖rconv (Gam K n) μ a φ x‖ ≤ C * qht x ^ N * ‖φ‖

def CuspDecay (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n) : Prop :=
  ∀ N' : ℕ, ∃ C : ℝ, ∀ φ ∈ cuspidalL2 μ, ∀ x : G1 K n,
    ‖rconv (Gam K n) μ a φ x‖ ≤ C * (qht x ^ N')⁻¹ * ‖φ‖

def Kern : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (θ : Twist μ)
    (a g : CC K n), PolyBd μ a → CuspDecay μ a → PolyBd μ (CuspidalProjection.ccStar g) →
    ∀ N' : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ (f : CC K n) (M : L2 μ →L[ℂ] L2 μ) (Z : ℝ), 1 ≤ Z →
      M ∘L Pc μ = Pc μ ∘L M → Rop μ f = Rop μ a ∘L M ∘L Rop μ g →
      (∀ x : G1 K n, Z < qht x → twK θ f x = 0) →
      ‖twInt θ f - cuspTr μ θ f‖ ≤
        C * Z ^ N * ‖M ∘L (ContinuousLinearMap.id ℂ (L2 μ) - Pc μ)‖ + C * (Z ^ N')⁻¹ * ‖M‖

end PositivityTheory.Rg.Tf.Core
