import Formalism.JumpKernelCokernel.Statement

noncomputable section

namespace Formalism.KernelCokernelLengths

def LemmaDJoint : Prop :=
  ∀ (O : Type) [CommRing O] (R : Type) [AddCommGroup R] [Module O R] (π : Module.End O R)
    (R' R'' : Submodule O R) (B : Type) [AddCommGroup B] [Module O B] (πB : Module.End O B)
    (j : ↥R'' →ₗ[O] B), R' ≤ R'' → R''.map π ≤ R'' → Module.length O B ≠ ⊤ →
    LinearMap.ker j = R'.comap R''.subtype →
    (∀ (x : ↥R'') (hx : π x ∈ R''), j ⟨π x, hx⟩ = πB (j x)) →
      Module.length O (R ⧸ (R' ⊔ LinearMap.range π)) ≤
        Module.length O (R ⧸ (R'' ⊔ LinearMap.range π)) + Module.length O (LinearMap.ker πB)

def RowDJoint : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ B₀ : ℕ, ∀ ℓ : ℕ, 11 ≤ ℓ → ∀ (b η S t bi h : ℕ) (s₁ E e₂ : ℝ), B₀ ≤ b →
    (η : ℝ) ≤ δ * b → (S : ℝ) ≤ δ * b → (t : ℝ) ≤ δ * b →
    b ≤ bi + t + 1 → bi + S ≤ h → h ≤ b + η + t + S + 1 →
    let η' := η + t + 1
    let a := ⌈Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + η')⌉₊
    s₁ ≤ (2 * (a : ℝ) + 2 * (η' : ℝ) + (S : ℝ)) / ((ℓ : ℝ) - 1) + 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam ℓ (h + η') →
    E ≤ (3 * (a : ℝ) + (S : ℝ) + 2 * (η' : ℝ)) / ((ℓ : ℝ) - 1) + 3 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam ℓ (h + η') →
    e₂ ≤ (bi : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) + E + 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ ℓ (h + η') + 2 * (S : ℝ)
        + 5 + Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam ℓ (h + η') →
    (2 * η' ≤ h ∧ h ≤ 2 * bi ∧ 2 * a + η' + 1 ≤ bi) ∧
      s₁ + 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig ℓ h η' + e₂ + (S : ℝ) + E + Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ ℓ (h + η') ≤
        50 * (h : ℝ) / (ℓ : ℝ) ^ 2 + 4 * (S : ℝ) + 10 * (η' : ℝ) / ((ℓ : ℝ) - 1)
          + 24 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam ℓ (h + η')

end Formalism.KernelCokernelLengths
