import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.HaP

open MvPolynomial Formalism.L2.Pj

def SatRetrSt : Prop :=
  ∀ (ι : Type) [Fintype ι] (W : Submodule ℤ (ι → ℤ)), (∀ (z : ℤ) (x : ι → ℤ), z ≠ 0 → z • x ∈ W → x ∈ W) →
    ∃ ρ : (ι → ℤ) →ₗ[ℤ] (ι → ℤ), (∀ x, ρ x ∈ W) ∧ ∀ x ∈ W, ρ x = x

def RowInvUpSt : Prop :=
  ∀ (Ty : Type) (r : Ty → ℕ) (n : ℕ) (K : Type) [Field K] [CharZero K] (P : MvPolynomial (Letter Ty r n) K),
    (∀ (σ : Ty) (i i' : Fin (r σ)), i' < i → ∀ q : ℚ, rowShift r n K σ i i' (q : K) P = P) → RowInv r n K P

end Formalism.L2.FormalSeriesBounds.HaP
