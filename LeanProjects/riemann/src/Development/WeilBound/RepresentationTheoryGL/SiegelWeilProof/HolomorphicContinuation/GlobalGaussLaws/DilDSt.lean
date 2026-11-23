import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IteratedDerivOfReal

noncomputable section

open Topology

namespace PositivityTheory.Rg.Sw.Glob

def ContDeriv : Prop :=
  ∀ (m n : ℕ) (U : Set ℂ), IsOpen U → ∀ f : ℂ → (Fin m → Fin n → ℂ) → ℂ,
    ContinuousOn (fun p : ℂ × (Fin m → Fin n → ℂ) => f p.1 p.2) (U ×ˢ Set.univ) →
    (∀ u, DifferentiableOn ℂ (fun z => f z u) U) →
    ∀ r : ℕ, ContinuousOn (fun p : ℂ × (Fin m → Fin n → ℂ) => iteratedDeriv r (fun z => f z p.2) p.1) (U ×ˢ Set.univ)

def SchScale : Prop :=
  ∀ (m n : ℕ) (f : (Fin m → Fin n → ℂ) → ℂ) (s : ℝ) (X : Fin n → ℝ) (a : ℂ), IsSch f →
    IsSch (fun u => a * f (fun i j => u i j * Real.exp (s * X j)))

end PositivityTheory.Rg.Sw.Glob
