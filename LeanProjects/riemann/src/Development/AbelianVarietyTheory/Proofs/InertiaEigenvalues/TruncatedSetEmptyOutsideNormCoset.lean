import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem norm_sub_notMem_of_not_norm :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s : A.K, A.NL (algebraMap A.K A.L s) = s ^ 2) ∧ (∀ y y' : A.L, A.NL (y * y') = A.NL y * A.NL y') ∧ (∀ t : unitary A.L, A.NL (t : A.L) = 1) ∧ (∀ y : A.L, IsUnit (A.NL y) → IsUnit y) ∧ (∀ y : A.L, IsUnit y → IsUnit (A.NL y))) → ∀ (x : A.Kˣ) (a : A.K) (D : Set A.K), (∀ b ∈ D, ∃ s s' : A.K, s * s' = 1 ∧ s ^ 2 = 1 + Ring.inverse a * b) → IsUnit a → (¬ ∃ y : A.L, IsUnit y ∧ a = x * A.NL y) → ∀ y : A.L, (x : A.K) * A.NL y - a ∉ D := by
  intro F E _ _ _ _ _ A ⟨h1, h2, _, h4, _⟩ x a D hD ha hn y hy
  obtain ⟨s, s', hss, hs⟩ := hD _ hy
  have hai : a * Ring.inverse a = 1 := Ring.mul_inverse_cancel a ha
  have key : (x : A.K) * A.NL y = a * s ^ 2 := by
    rw [hs]
    linear_combination (-((x : A.K) * A.NL y - a)) * hai
  have hsu : IsUnit s := IsUnit.of_mul_eq_one s' hss
  have hs'u : IsUnit s' := IsUnit.of_mul_eq_one s (by rw [mul_comm]; exact hss)
  have hN : IsUnit (A.NL y) := by
    have : IsUnit ((x : A.K) * A.NL y) := by
      rw [key]; exact ha.mul (hsu.pow 2)
    exact isUnit_of_mul_isUnit_right this
  refine hn ⟨y * algebraMap A.K A.L s', (h4 y hN).mul (hs'u.map _), ?_⟩
  rw [h2, h1, ← mul_assoc, key]
  linear_combination (-a * (s * s' + 1)) * hss

end GlobalTheory.JR
