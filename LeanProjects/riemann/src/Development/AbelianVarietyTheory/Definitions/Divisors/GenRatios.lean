import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegVal

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp
open scoped NNReal

section Generic

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def ratioField (ev : V →ₗ[K] Ω) : IntermediateField K Ω :=
  IntermediateField.adjoin K {a | ∃ v w, a = ev v / ev w}

def GenRatios (ev : V →ₗ[K] Ω) : Prop := ev ≠ 0 ∧ ratioField ev = ⊤

def ValBound (ev : V →ₗ[K] Ω) (τ : ℕ) (t : Ω) : Prop :=
  ∀ ν : Valuation Ω ℝ≥0, (∀ a : K, a ≠ 0 → ν (algebraMap K Ω a) = 1) → ∃ v, ν t ≤ ν (ev v) ^ τ

example : GenRatios (LinearMap.id : K →ₗ[K] K) :=
  ⟨fun h => one_ne_zero (LinearMap.congr_fun h 1), eq_top_iff.2 fun a _ =>
    IntermediateField.subset_adjoin _ _ ⟨a, 1, by simp⟩⟩

example (ev : V →ₗ[K] Ω) (v : V) : ValBound ev 1 (ev v) := fun _ _ => ⟨v, by simp⟩

end Generic

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def BirOn (Z : Comp Xo c) (G : WTZ E) : Prop := GenRatios (genPoint Z (cuspOn U Z G))

def ValMult (Z : Comp Xo c) (G G' : WTZ E) : Prop :=
  ∃ (a : ℕ) (θ : Rul Xo c), 1 ≤ a ∧ genVal Z θ ≠ 0 ∧ ∀ (k : ℕ), 1 ≤ k → ∀ f ∈ cuspOn U Z ((a * k) • G'),
    θ ^ k * f ∈ cuspOn U Z ((a * k) • G) ∧ ValBound (genPoint Z (cuspOn U Z G)) (a * k) (genVal Z (θ ^ k * f))

end GlobalTheory.DegVal
