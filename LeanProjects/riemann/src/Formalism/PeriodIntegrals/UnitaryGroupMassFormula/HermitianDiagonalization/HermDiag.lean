import Mathlib
import Formalism.LocalToGlobal.AdelicCompactOpens.HermDefONFamily

namespace PI.UnitaryGroupMassFormula.HermConj

open Matrix

def HermDiag : Prop :=
  ∀ (E : Type) [Field E] [CharZero E] (σ : E →+* E), (∀ x, σ (σ x) = x) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (J.map σ)ᵀ = J →
      ∃ (Q : Matrix (Fin n) (Fin n) E) (d : Fin n → E), IsUnit Q.det ∧ (∀ i, σ (d i) = d i) ∧
        J = (Q.map σ)ᵀ * diagonal d * Q

end PI.UnitaryGroupMassFormula.HermConj
