import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CarrierRow

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open Formalism.MainNotions.S

def RowsDep : Prop :=
  ∀ (E : Type) [Field E] (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (u : Fin r → E), u ≠ 0 →
    (∀ b, ∑ c, u c * Z (Fin.castSucc c) b = 0) → leadMinorE Z (r + 1) = 0 ∧ leadMinorE Z r = 0

def RightInv : Prop :=
  ∀ (E : Type) [Field E] (r : ℕ) (β : Matrix (Fin r) (Fin (r + 1)) E),
    (∀ u : Fin r → E, (∀ b, ∑ c, u c * β c b = 0) → u = 0) →
    ∃ (Q : Matrix (Fin (r + 1)) (Fin r) E) (v l : Fin (r + 1) → E),
      β * Q = 1 ∧ (∀ c, ∑ b, β c b * v b = 0) ∧ ∀ i j, (Q * β) i j = (if i = j then 1 else 0) - v i * l j

def SkewSolve : Prop :=
  ∀ (E : Type) [Field E] [StarRing E] (r : ℕ) (β x : Matrix (Fin r) (Fin (r + 1)) E)
    (Q : Matrix (Fin (r + 1)) (Fin r) E) (v l : Fin (r + 1) → E),
    (∀ u : Fin r → E, (∀ b, ∑ c, u c * β c b = 0) → u = 0) →
    β * Q = 1 → (∀ c, ∑ b, β c b * v b = 0) → (∀ i j, (Q * β) i j = (if i = j then 1 else 0) - v i * l j) →
    (∀ a b, ∑ c, (star (β c a) * x c b + star (x c a) * β c b) = 0) →
      (∀ c d, (x * Q) c d + star ((x * Q) d c) = 0) ∧ x = (x * Q) * β

end PI.TermsAtPtFiniteW
