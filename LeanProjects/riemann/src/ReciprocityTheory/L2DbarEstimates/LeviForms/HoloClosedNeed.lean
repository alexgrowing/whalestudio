import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Filter Topology
open scoped ENNReal

def HoloClosedNeed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (ps : M → ℝ) (F : ℕ → M → ℂ) (f : M → ℂ),
    SmoothR n X.z ps → (∀ k, Holo n X.z (F k)) → Measurable f →
    Tendsto (fun k => wint n X.z (fun x => F k x - f x) ps) atTop (𝓝 0) →
    ∃ G : M → ℂ, Holo n X.z G ∧ f =ᵐ[vol n X.z] G

def EvalNeed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (ps : M → ℝ) (x0 : M), SmoothR n X.z ps →
    ∃ C : ℝ, ∀ F : M → ℂ, Holo n X.z F →
      ENNReal.ofReal (‖F x0‖ ^ 2) ≤ ENNReal.ofReal C * wint n X.z F ps

def CVXNeed.{u} : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H], CVXStatement H

end ReciprocityTheory.L2DbarEstimates.I
