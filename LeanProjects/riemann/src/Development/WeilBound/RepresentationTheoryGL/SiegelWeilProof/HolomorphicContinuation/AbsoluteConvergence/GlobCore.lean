import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightAlt

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

structure GlobCore (ε : Fin m → Bool) (c : ℝ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ)) (ρ : GR n → PX m n →ₗ[ℂ] PX m n)
    (G : Type) [Group G] [TopologicalSpace G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
    (sec I : PX m n →ₗ[ℂ] (G → ℂ)) : Prop where
  ιcont : Continuous ι
  split : ∀ g, ∃ (x : G) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g = x * ι y ∧
    ∀ y' : GR n, (Ht (x * ι y') : ℝ) = r * hLoc y' ∧ ∀ P, sec P (x * ι y') = S * sL P y'
  Icont : Continuous (I 1)
  Ileft : ∀ γ ∈ Γ, ∀ g, I 1 (γ * g) = I 1 g
  Ik : ∀ P g (k : GR n), InK (mR k) → I P (g * ι k) = I (ρ k P) g
  Iinv : ∀ g a b P, I (hOp ε c a b P) g = 0
  Idil : ∀ (g : G) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ t, IsDil X t (a t)) → ∃ (U : Set ℂ) (F : GR n → ℂ → ℂ), IsOpen U ∧
    (∀ t : ℝ, (t : ℂ) ∈ U) ∧ ContinuousOn (fun y : GR n × ℂ => F y.1 y.2) (univ ×ˢ U) ∧ ∀ y, DifferentiableOn ℂ (F y) U ∧
      (∀ t : ℝ, F y t = I 1 (g * ι (y * a t))) ∧ ∀ r : ℕ, iteratedDeriv r (F y) 0 = I ((dil c X ^ r) 1) (g * ι y)
  eis : ∃ (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → G → ℂ) (σ : ℝ), IsOpen U ∧ GlobalTheory.Cont.IsRightDomain U ∧ s₀ ∈ U ∧ d ≠ 0 ∧
    (∀ g, DifferentiableOn ℂ (E · g) U) ∧ ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ univ) ∧
    (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g) ∧
    ∀ z : ℂ, σ < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ q,
        ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g q‖ ≤ u q) ∧
      ∀ g, E z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g

end PositivityTheory.Rg.Sw.AbsSt
