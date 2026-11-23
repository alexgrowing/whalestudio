import ReciprocityTheory.L2DbarEstimates.SkodaWeights.NeedBergmanClosed
import ReciprocityTheory.L2DbarEstimates.LeviForms.HoloClosedNeed
import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

def ClosedCoreStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z → ∀ (ψ : M → ℝ), Continuous ψ →
    ∀ (F : ℕ → M → ℂ) (f : M → ℂ), (∀ k, Holo n z (F k)) → AEStronglyMeasurable f (vol n z) →
    Tendsto (fun k => wint n z (fun x => F k x - f x) ψ) atTop (𝓝 0) →
    ∃ G : M → ℂ, Holo n z G ∧ f =ᵐ[vol n z] G

def EvalPtStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z → ∀ (ψ : M → ℝ), Continuous ψ → ∀ x0 : M,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : M → ℂ, Holo n z F →
      ENNReal.ofReal (‖F x0‖ ^ 2) ≤ ENNReal.ofReal C * wint n z F ψ

end

end ReciprocityTheory.L2DbarEstimates.F
