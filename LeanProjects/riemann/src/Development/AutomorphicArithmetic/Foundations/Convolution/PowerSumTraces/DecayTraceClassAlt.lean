import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.CuspDecay

noncomputable section

open MeasureTheory NumberField
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core

namespace UpperTheory.ConvolutionTheory.C

def fcalc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (φ : ℝ → ℝ) (A : H →L[ℂ] H) :
    H →L[ℂ] H := cfc φ A

def TwistUnitary : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (θ : Twist μ),
    ∃ U : L2 μ ≃ₗᵢ[ℂ] L2 μ, (U : L2 μ →L[ℂ] L2 μ) = θ.U ∧
      (∀ g v, U (rightRegularRep (Gam K n) μ g v) = rightRegularRep (Gam K n) μ (θ.e g) (U v)) ∧
      (cuspidalL2 μ).map (U : L2 μ →ₗ[ℂ] L2 μ) = cuspidalL2 μ

def CuspTrSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (θ : Twist μ), MultOneAt μ →
    (∀ B : L2 μ →L[ℂ] L2 μ, (∀ V, IsSummand μ V → ∀ v ∈ V, B v ∈ V) → IsTraceClass (Pc μ ∘L B ∘L Pc μ) →
      HasSum (fun V : {V // IsSummand μ V ∧ V.map (θ.U : L2 μ →ₗ[ℂ] L2 μ) = V} => trOn V.1 (B ∘L θ.U))
        (trace (Pc μ ∘L B ∘L θ.U ∘L Pc μ))) ∧
    ∀ f : CC K n, IsTraceClass (Pc μ ∘L Rop μ f ∘L Pc μ) →
      HasSum (fun V : {V // IsSummand μ V ∧ V.map (θ.U : L2 μ →ₗ[ℂ] L2 μ) = V} => trOn V.1 (Rop μ f ∘L θ.U))
        (cuspTr μ θ f)

def PolyBdAll : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n), PolyBd μ a

def SmoothDecay : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n),
    IsLeftSmooth a → CuspDecay μ a

def DecayTraceClass : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a g : CC K n)
    (M : L2 μ →L[ℂ] L2 μ), CuspDecay μ a → CuspDecay μ (CuspidalProjection.ccStar g) → M ∘L Pc μ = Pc μ ∘L M →
    IsTraceClass (Pc μ ∘L (Rop μ a ∘L M ∘L Rop μ g) ∘L Pc μ)

def CuspTrBand : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (θ : Twist μ), MultOneAt μ →
    ∀ A : L2 μ →L[ℂ] L2 μ, 0 ≤ A → (∀ V, IsSummand μ V → ∀ v ∈ V, A v ∈ V) → IsCompactOperator (A ∘L Pc μ) →
    ∀ η : ℝ, 0 < η → ∃ S : Finset (ℝ × Submodule ℂ (L2 μ)),
      (∀ p, p ∈ S ↔ η < p.1 ∧ IsSummand μ p.2 ∧ p.2.map (θ.U : L2 μ →ₗ[ℂ] L2 μ) = p.2 ∧ eigIn p.2 A p.1 ≠ ⊥) ∧
      (∀ p ∈ S, FiniteDimensional ℂ (eigIn p.2 A p.1)) ∧
      ∀ (φ : ℝ → ℝ) (c : ℝ) (T : L2 μ →L[ℂ] L2 μ), Continuous φ → 0 ≤ c → (∀ x ∈ Set.Icc 0 η, |φ x| ≤ c) →
        (∀ V, IsSummand μ V → ∀ v ∈ V, T v ∈ V) → IsTraceClass (Pc μ ∘L T ∘L Pc μ) →
        ‖trace (Pc μ ∘L fcalc φ A ∘L T ∘L θ.U ∘L Pc μ) - ∑ p ∈ S, (φ p.1 : ℂ) * trOn (eigIn p.2 A p.1) (T ∘L θ.U)‖ ≤
          c * (traceNorm (Pc μ ∘L T ∘L Pc μ)).toReal

end UpperTheory.ConvolutionTheory.C
