import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem div_d_continuous_of_bdd_ltorsion :
    ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (d : A) (N : ℕ), d ∈ nonZeroDivisors A →
      (∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d}) →
      ∀ (n : ℕ) (z : A), d * z ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ (2 * (n + N + 1)) →
        z ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n := by
  intro l _ A _ d N hd hN n z hz
  set m := n + N + 1 with hm
  have h2 : 2 * m = m + m := by ring
  rw [h2] at hz
  have h1 := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(l : A)}) (J := Ideal.span {d})
    (m := m) (n := m) hz
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h1
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hv

  have hdm : d ^ m = d * d ^ (n + N) := by rw [hm, pow_succ]; ring
  have hla : (l : A) ^ m * a ∈ Ideal.span {d} := by
    rw [Ideal.mem_span_singleton']
    exact ⟨z - b * d ^ (n + N), by rw [hdm] at huv; linear_combination -huv⟩
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (hN a m hla)

  have hmN : m = (n + 1) + N := by rw [hm]; ring
  have key : d * (z - (l : A) ^ (n + 1) * a' - b * d ^ (n + N)) = 0 := by
    have : (l : A) ^ m * a = (l : A) ^ (n + 1) * (a' * d) := by
      rw [ha', hmN, pow_add]; ring
    rw [hdm] at huv
    linear_combination (-1 : A) * huv + this
  have hz' : z = (l : A) ^ (n + 1) * a' + b * d ^ (n + N) := by
    have := (mem_nonZeroDivisors_iff.1 hd).1 _ key
    linear_combination this
  rw [hz']
  refine Ideal.add_mem _ ?_ ?_
  · refine Ideal.mul_mem_right _ _ ?_
    have : (l : A) ^ (n + 1) ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ (n + 1) :=
      Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) _
    exact Ideal.pow_le_pow_right (Nat.le_succ n) this
  · refine Ideal.mul_mem_left _ _ ?_
    have : d ^ (n + N) ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ (n + N) :=
      Ideal.pow_mem_pow (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) _
    exact Ideal.pow_le_pow_right (Nat.le_add_right n N) this

end GlobalTheory
