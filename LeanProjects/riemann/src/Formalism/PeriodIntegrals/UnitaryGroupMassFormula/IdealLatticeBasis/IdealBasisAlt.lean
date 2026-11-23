import Mathlib
import Formalism.PeriodIntegrals.IdealLattice
import Formalism.PeriodIntegrals.AreaLat

open NumberField

namespace PI.IdealLatticeWork

def OKArea : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ), Module.finrank ℚ K = 2 → IsEmpty (K →+* ℝ) →
    ∀ b : Module.Basis (Fin 2) ℤ (𝓞 K),
      |((starRingEnd ℂ) (φ (b 0 : K)) * φ (b 1 : K)).im| = Real.sqrt |(NumberField.discr K : ℝ)| / 2

def IdealBasis : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (cc : Ideal (𝓞 K)), cc ≠ ⊥ →
    ∃ c₁ ∈ cc, ∃ c₂ ∈ cc, (∀ c ∈ cc, ∃ m n : ℤ, c = m • c₁ + n • c₂) ∧
      ∃ p q r s : ℤ, c₁ = p • b 0 + q • b 1 ∧ c₂ = r • b 0 + s • b 1 ∧
        (p * s - q * r).natAbs = Ideal.absNorm cc

def OKBasis : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → Nonempty (Module.Basis (Fin 2) ℤ (𝓞 K))

def Assemble : Prop := OKArea → IdealBasis → OKBasis → PI.AreaLat → PI.IdealLattice

end PI.IdealLatticeWork
