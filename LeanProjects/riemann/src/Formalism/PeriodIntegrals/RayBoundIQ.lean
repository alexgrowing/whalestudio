import Mathlib

open NumberField

namespace PI

def RayBoundIQ : Prop :=
  ∀ (K0 : Type) [Field K0] [NumberField K0], Module.finrank ℚ K0 = 2 → IsEmpty (K0 →+* ℝ) →
    ∀ qq : Ideal (𝓞 K0), qq ≠ ⊥ →
      1 ≤ Nat.card (Quot (fun I J : {I : Ideal (𝓞 K0) // I ≠ ⊥ ∧ I ⊔ qq = ⊤} =>
        ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
          (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
          Ideal.span {a} * I.1 = Ideal.span {b} * J.1)) ∧
      (Nat.card (Quot (fun I J : {I : Ideal (𝓞 K0) // I ≠ ⊥ ∧ I ⊔ qq = ⊤} =>
        ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
          (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
          Ideal.span {a} * I.1 = Ideal.span {b} * J.1)) : ℝ) ≤
        4 * |(discr K0 : ℝ)| * (Ideal.absNorm qq : ℝ)

end PI
