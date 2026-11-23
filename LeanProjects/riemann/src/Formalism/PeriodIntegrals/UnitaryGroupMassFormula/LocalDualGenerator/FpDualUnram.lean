import Mathlib

noncomputable section

open ValuativeRel

namespace PI.LocDualGen.W

def PsiKer : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (t : ℚ_[l]) (a : ℚ), (∃ n : ℕ, a.den = l ^ n) → ‖t - (a : ℚ_[l])‖ ≤ 1 →
    (Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) = 1 ↔ ‖t‖ ≤ 1)

def FpDual : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (l : ℕ) [Fact l.Prime]
    [Algebra ℚ_[l] K], IsNonarchimedeanLocalField K → CharZero K →
    Continuous (algebraMap ℚ_[l] K) → FiniteDimensional ℚ_[l] K →
    ∃ d : K, d ≠ 0 ∧ ∀ a : K,
      (∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (a * (b : K) * d⁻¹)‖ ≤ 1) ↔ a ∈ 𝒪[K]

def FpDualUnram : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (l : ℕ) [Fact l.Prime]
    [Algebra ℚ_[l] K], IsNonarchimedeanLocalField K → CharZero K →
    Continuous (algebraMap ℚ_[l] K) → FiniteDimensional ℚ_[l] K →
    Irreducible ((l : ℕ) : 𝒪[K]) →
    ∀ a : K, (∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (a * (b : K))‖ ≤ 1) ↔ a ∈ 𝒪[K]

def EpSelfDual : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (L : Type) [CommRing L]
    [Algebra K L], IsNonarchimedeanLocalField K → CharZero K →
    Module.Free K L → Module.finrank K L = 2 → IsReduced L →
    ∀ O : Subring L, (∀ x : L, x ∈ O ↔ IsIntegral 𝒪[K] x) →
    (∀ ϖ : 𝒪[K], Irreducible ϖ → ∀ x ∈ O,
      x * x ∈ Submodule.span O {algebraMap K L (ϖ : K)} →
        x ∈ Submodule.span O {algebraMap K L (ϖ : K)}) →
    ∀ x : L, (∀ y ∈ O, Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ x ∈ O

end PI.LocDualGen.W
