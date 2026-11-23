import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.CuspDecay
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport

noncomputable section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core
open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.K

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def kv (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n) (x : G1 K n) : L2 μ :=
  (InnerProductSpace.toDual ℂ (L2 μ)).symm (rconvCLM (Gam K n) μ a x)

theorem inner_kv (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n) (x : G1 K n) (φ : L2 μ) :
    ⟪kv μ a x, φ⟫_ℂ = rconv (Gam K n) μ a φ x := by
  rw [kv, InnerProductSpace.toDual_symm_apply, rconvCLM_apply]

def Kern2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (θ : Twist μ)
    (a g : CC K n), PolyBd μ a → CuspDecay μ a → PolyBd μ (ccStar g) → CuspDecay μ (ccStar g) →
    ∃ N : ℕ, ∀ N' : ℕ, ∃ C : ℝ, ∀ (f : CC K n) (M : L2 μ →L[ℂ] L2 μ) (Z : ℝ), 1 ≤ Z →
      M ∘L Pc μ = Pc μ ∘L M → Rop μ f = Rop μ a ∘L M ∘L Rop μ g →
      (∀ x : G1 K n, Z < qht x → twK θ f x = 0) →
      ‖twInt θ f - cuspTr μ θ f‖ ≤
        C * Z ^ N * ‖M ∘L (ContinuousLinearMap.id ℂ (L2 μ) - Pc μ)‖ + C * (Z ^ N')⁻¹ * ‖M‖

def IsGal {μ : Measure (G1 K n)} [μ.IsHaarMeasure] (σ : K ≃+* K) (θ : Twist μ) : Prop :=
  ∀ g : G1 K n, ((θ.e g : G1 K n) : AdelicGLn.AdelicGL K n) =
    Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ) (g : AdelicGLn.AdelicGL K n)

def GalTwistEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (σ : K ≃+* K),
    ∃ θ : Twist μ, IsGal σ θ

end UpperTheory.ConvolutionTheory.K
