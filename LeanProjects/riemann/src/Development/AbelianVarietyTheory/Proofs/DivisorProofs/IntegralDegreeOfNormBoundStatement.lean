import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDegreeOfNormBound
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_degree_of_norm_bound : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (R : Subalgebra K Ω) [Algebra.FiniteType K R] (σ : K →+* ℂ) (a : Ωˣ) (n τ : ℕ) (w : Fin n → V) (w' : Fin n → R) (t : Ω) (t' : R) (C : ℝ), (∀ i, (w' i : Ω) = (a : Ω) * ev (w i)) → (t' : Ω) = (a : Ω) ^ τ * t → (∀ φ : R →+* ℂ, φ.comp (algebraMap K R) = σ → ‖φ t'‖ ^ 2 ≤ C * (∑ i, ‖φ (w' i)‖ ^ 2) ^ τ) → IsIntDeg ev τ t := by
  first | exact @GlobalTheory.DegCmp.isIntDeg_of_bounded | exact GlobalTheory.DegCmp.isIntDeg_of_bounded | (intros; apply GlobalTheory.DegCmp.isIntDeg_of_bounded <;> assumption)
