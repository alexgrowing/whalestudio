import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal

noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.ConeMono

variable {X : Type} [AddCommGroup X]

def ev (a b : X) : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := LinearMap.applyₗ b ∘ₗ LinearMap.applyₗ a

@[simp] theorem ev_apply (a b : X) (β : LinearMap.BilinForm ℤ X) : ev a b β = β a b := rfl

def expo (n : X × X →₀ ℤ) : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := n.sum fun p k => k • ev p.1 p.2

def mono {K : Type} [Field K] (q : X → X → Kˣ) (n : X × X →₀ ℤ) : Kˣ := n.prod fun p k => q p.1 p.2 ^ k

def termIdeal [Module.Finite ℤ X] (V : Type) [CommRing V] {K : Type} [Field K] [Algebra V K] (φ : InvFun ℤ) (d : ℕ) (q : X → X → Kˣ) :
    Ideal V :=
  Ideal.span {v | ∃ n : X × X →₀ ℤ, (∀ β ∈ balForms (id : ℤ → ℤ) X, (∀ y, 0 ≤ β y y) →
      (d : ℝ) * φ.evalZ β ≤ (expo n β : ℝ)) ∧ algebraMap V K v = (mono q n : K)}

end GlobalTheory.ConeMono
