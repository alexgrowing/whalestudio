import Mathlib
import Formalism.PeriodIntegrals.Transference
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.TransferenceKey

open Module
open scoped Real

noncomputable section

namespace PI.Tr

def dualLat {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Λ : Submodule ℤ E) :
    Submodule ℤ E where
  carrier := {y | ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ)}
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨z1, h1⟩ := ha x hx
    obtain ⟨z2, h2⟩ := hb x hx
    exact ⟨z1 + z2, by rw [inner_add_right, h1, h2]; push_cast; ring⟩
  zero_mem' := fun x _ => ⟨0, by simp⟩
  smul_mem' := by
    intro c a ha x hx
    obtain ⟨z, h⟩ := ha x hx
    exact ⟨c * z, by rw [← Int.cast_smul_eq_zsmul ℝ c a, real_inner_smul_right, h]; push_cast; ring⟩

lemma mem_dualLat {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Λ : Submodule ℤ E}
    {y : E} : y ∈ dualLat Λ ↔ ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ) := Iff.rfl

def PoissonGauss : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    (∀ t : ℝ, 0 < t → ∀ v : E, Summable fun x : Λ => Real.exp (-π * t * ‖(x : E) + v‖ ^ 2)) ∧
    (∀ t : ℝ, 0 < t → Summable fun y : dualLat Λ => Real.exp (-π * ‖(y : E)‖ ^ 2 / t)) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t → ∀ v : E,
      ∑' x : Λ, Real.exp (-π * t * ‖(x : E) + v‖ ^ 2) =
        c * t ^ (-(finrank ℝ E : ℝ) / 2) *
          ∑' y : dualLat Λ, Real.exp (-π * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * π * inner ℝ (y : E) v)

def PoissonBasis : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (ι : Type) [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) (b' : ι → E),
    (∀ i j, inner ℝ (b i) (b' j) = if i = j then (1 : ℝ) else 0) →
    (∀ t : ℝ, 0 < t → ∀ v : E,
      Summable fun k : ι → ℤ => Real.exp (-π * t * ‖(∑ i, (k i : ℝ) • b i) + v‖ ^ 2)) ∧
    (∀ t : ℝ, 0 < t → Summable fun m : ι → ℤ => Real.exp (-π * ‖∑ i, (m i : ℝ) • b' i‖ ^ 2 / t)) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t → ∀ v : E,
      ∑' k : ι → ℤ, Real.exp (-π * t * ‖(∑ i, (k i : ℝ) • b i) + v‖ ^ 2) =
        c * t ^ (-(finrank ℝ E : ℝ) / 2) *
          ∑' m : ι → ℤ, Real.exp (-π * ‖∑ i, (m i : ℝ) • b' i‖ ^ 2 / t) *
            Real.cos (2 * π * inner ℝ (∑ i, (m i : ℝ) • b' i) v)

def DualTransport : Prop := PoissonBasis → PoissonGauss

def KeyDim (P : ℕ → Prop) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (lam : ℝ) (u : E), P (finrank ℝ E) →
    0 < lam →
    (∀ y : E, (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) → ‖y‖ < lam →
      ∃ m : ℤ, inner ℝ u y = (m : ℝ)) →
    ∃ l ∈ Λ, ‖u - l‖ * lam ≤ (finrank ℝ E : ℝ) / 2

def KeyLarge : Prop := KeyDim (fun n => 2 ≤ n)

def KeySmall : Prop := KeyDim (fun n => n ≤ 1)

def GaussStep : Prop := PoissonGauss → KeyLarge

end PI.Tr
