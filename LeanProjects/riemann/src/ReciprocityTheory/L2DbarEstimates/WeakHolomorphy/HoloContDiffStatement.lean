import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement

namespace ReciprocityTheory.L2DbarEstimates.C

open Set
open scoped ContDiff

def HoloSmoothStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (EuclideanSpace ℂ (Fin n))) (f : EuclideanSpace ℂ (Fin n) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ f Ω → ContDiffOn ℝ ∞ f Ω

def HoloDerivStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (EuclideanSpace ℂ (Fin n))) (f : EuclideanSpace ℂ (Fin n) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ f Ω →
      ∀ v : EuclideanSpace ℂ (Fin n), DifferentiableOn ℂ (fun x => fderiv ℂ f x v) Ω

def HoloContDiffStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (EuclideanSpace ℂ (Fin n))) (f : EuclideanSpace ℂ (Fin n) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ f Ω → ContDiffOn ℂ ∞ f Ω

end ReciprocityTheory.L2DbarEstimates.C
