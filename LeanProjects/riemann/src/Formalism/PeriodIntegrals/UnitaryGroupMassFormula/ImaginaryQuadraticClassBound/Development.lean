import Mathlib
import Formalism.PeriodIntegrals.RayBoundIQ

open NumberField

namespace PI.RayBoundIQW

def rayRel (K0 : Type) [Field K0] [NumberField K0] (qq : Ideal (𝓞 K0))
    (I J : {I : Ideal (𝓞 K0) // I ≠ ⊥ ∧ I ⊔ qq = ⊤}) : Prop :=
  ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
    (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
    Ideal.span {a} * I.1 = Ideal.span {b} * J.1

def FibreBound : Prop :=
  ∀ (K0 : Type) [Field K0] [NumberField K0], IsEmpty (K0 →+* ℝ) →
    ∀ qq : Ideal (𝓞 K0), qq ≠ ⊥ →
      Finite (Quot (rayRel K0 qq)) ∧
        Nat.card (Quot (rayRel K0 qq)) ≤ classNumber K0 * Ideal.absNorm qq

def ClassNumBound : Prop :=
  ∀ (K0 : Type) [Field K0] [NumberField K0], Module.finrank ℚ K0 = 2 → IsEmpty (K0 →+* ℝ) →
    (classNumber K0 : ℝ) ≤ 4 * |(discr K0 : ℝ)|

end PI.RayBoundIQW
