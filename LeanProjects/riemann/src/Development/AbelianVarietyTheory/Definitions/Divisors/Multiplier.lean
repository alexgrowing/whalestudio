import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegCmp

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt
open scoped ENNReal

section Generic

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def hilb (ev : V →ₗ[K] Ω) (τ : ℕ) : ℕ∞ :=
  Cardinal.toENat (Module.rank K (↥((LinearMap.range ev) ^ τ : Submodule K Ω)))

def coneAlg (ev : V →ₗ[K] Ω) : Subalgebra K (Polynomial Ω) :=
  Algebra.adjoin K (Set.range fun v => Polynomial.X * Polynomial.C (ev v))

def IsIntDeg (ev : V →ₗ[K] Ω) (τ : ℕ) (t : Ω) : Prop :=
  IsIntegral (coneAlg ev) (Polynomial.X ^ τ * Polynomial.C t : Polynomial Ω)

def IsRatio (ev : V →ₗ[K] Ω) (τ : ℕ) (t : Ω) : Prop :=
  ∃ (e : ℕ) (h : Ω), h ∈ ((LinearMap.range ev) ^ e : Submodule K Ω) ∧ h ≠ 0 ∧
    t * h ∈ ((LinearMap.range ev) ^ (τ + e) : Submodule K Ω)

example (ev : V →ₗ[K] Ω) (v : V) : IsRatio ev 1 (ev v) ∧ IsIntDeg ev 1 (ev v) := by
  refine ⟨⟨0, 1, by simp [Submodule.one_eq_span], one_ne_zero, by simp⟩, ?_⟩
  have h : Polynomial.X * Polynomial.C (ev v) ∈ coneAlg ev := Algebra.subset_adjoin ⟨v, rfl⟩
  rw [IsIntDeg, pow_one]
  exact isIntegral_algebraMap (R := coneAlg ev) (x := ⟨_, h⟩)

end Generic

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)

def UnfAll : Prop := ∀ σ, GoodEmb c σ → IsUnf (U σ)

def Proport : Prop :=
  ∀ (Z : Comp Xo c) (la : Weight Dw), (∀ τ, StrictAnti (la τ)) →
    growthOn U Z (wtOf Dw la 0) = ENNReal.ofReal (topDeg U Z la)

def EqVolume : Prop := ∀ Z Z' : Comp Xo c, vZero U Z = vZero U Z'

def RatioOn (Z : Comp Xo c) (G : WTZ E) : Prop :=
  ∀ (τ : ℕ), ∀ t ∈ cuspOn U Z (τ • G), IsRatio (genPoint Z (cuspOn U Z G)) τ (genVal Z t)

def BoundedBy (Z : Comp Xo c) (σ : c.F →+* ℂ) (G₁ : WTZ E) (t : Rul Xo c) (G : WTZ E) (τ : ℕ) : Prop :=
  ∃ (n : ℕ) (w : Fin n → cuspOn U Z G) (C : ℝ), ∀ z ∈ framesOn (U σ) Z,
    homN (U σ) x G₁ t z ^ 2 ≤ C * (∑ i, homN (U σ) x G (w i : Rul Xo c) z ^ 2) ^ τ

def Multiplier (Z : Comp Xo c) (G G' : WTZ E) : Prop :=
  ∃ (a : ℕ) (θ : Rul Xo c), 1 ≤ a ∧ θ ∈ secZ Xo c (exZ Dw (a • (G - G'))) ∧ genVal Z θ ≠ 0 ∧
    (∀ (k : ℕ), ∀ f ∈ cuspOn U Z ((a * k) • G'), θ ^ k * f ∈ cuspOn U Z ((a * k) • G)) ∧
    ∃ σ, GoodEmb c σ ∧ BoundedBy U x Z σ (a • (G - G')) θ G a

def DegTie {K : Type} [Field K] [NumberField K] [StarRing K] {P : SlopeBoundParameters} (F : SlopeBoundLiftData K P) (u : Weight Dw) : Prop :=
  (∃ e : F.ι → Comp Xo c, ∀ k, F.δc k = compDeg U (e k) (wtOf Dw u 0)) ∧
    (∃ Z : Comp Xo c, F.δ' = delPrime U Z u) ∧ F.ρ = rhoB Dw u

end GlobalTheory.DegCmp
