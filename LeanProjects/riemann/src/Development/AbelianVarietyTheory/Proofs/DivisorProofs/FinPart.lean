import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory.LieRead

def lnGrP (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [NumberField K] {g : ℕ} (j : K →+* ℂ_[p])
    (L : Submodule (𝓞 K) (Fin g → K)) (k : Fin g) : ℝ :=
  Real.log (sInf {r : ℝ | ∃ c : Fin g → ℂ_[p], c k ≠ 0 ∧ (∀ i, k < i → c i = 0) ∧
    (∃ (n : ℕ) (a : Fin n → ℂ_[p]) (v : Fin n → Fin g → K), (∀ m, ‖a m‖ ≤ 1) ∧ (∀ m, v m ∈ L) ∧
      c = ∑ m, a m • fun i => j (v m i)) ∧ r = ‖c k‖⁻¹})

open Classical in

def finPart {K : Type} [Field K] [NumberField K] {g : ℕ} (L : Submodule (𝓞 K) (Fin g → K)) : ℝ :=
  ∑ᶠ p : ℕ, if hp : p.Prime then (haveI : Fact p.Prime := ⟨hp⟩; ∑ᶠ j : K →+* ℂ_[p], ∑ k, lnGrP p j L k) else 0

def adelSum {K : Type} [Field K] [NumberField K] {g : ℕ} (h : HermFam K (Fin g → K))
    (L : Submodule (𝓞 K) (Fin g → K)) : ℝ :=
  finPart L + (1 / 2) * ∑ σ : K →+* ℂ, Real.log (h.gram σ fun k => Pi.single k 1).det.re

end GlobalTheory.LieRead

end
