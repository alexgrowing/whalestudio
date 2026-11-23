import Mathlib

noncomputable section
open NumberField

namespace PI.KerLat

def PerPair : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Module.finrank ℚ K = 2 → (∃ k : K, (φ k).im ≠ 0) → cc ≠ ⊥ → δ ≠ 0 →
      ∃ L : PeriodPair, L.lattice.toAddSubgroup = AddSubgroup.closure {w : ℂ | ∃ c ∈ cc, w = δ * φ (c : K)}

def ExistsTwoTorsionOffKernels : Prop :=
  ∀ (L : PeriodPair) (d : ℕ), d % 8 = 7 →
    (∀ w ∈ L.lattice, ((1 + Complex.I * (Real.sqrt d : ℂ)) / 2) * w ∈ L.lattice) →
      ∃ t : ℂ, 2 * t ∈ L.lattice ∧ ((1 + Complex.I * (Real.sqrt d : ℂ)) / 2) * t ∉ L.lattice ∧
        ((1 - Complex.I * (Real.sqrt d : ℂ)) / 2) * t ∉ L.lattice

end PI.KerLat
