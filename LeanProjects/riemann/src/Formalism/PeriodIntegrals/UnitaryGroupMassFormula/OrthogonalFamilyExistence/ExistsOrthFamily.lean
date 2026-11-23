import Mathlib
import Formalism.PeriodIntegrals.NormGramAtOrigin

noncomputable section

namespace PI.NormGramAtOrigin.UnitaryGroupMassFormula

open Matrix

section Lemmas

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem hform_eq (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hform (starRingEnd E) J x y = ∑ j, (∑ i, starRingEnd E (x i) * J i j) * y j := by
  unfold hform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul]

theorem exists_pair (J : Matrix (Fin n) (Fin n) E) (hdet : J.det ≠ 0) (y : Fin n → E)
    (hy : y ≠ 0) : ∃ z, hform (starRingEnd E) J y z ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hdet
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  refine ⟨fun i => starRingEnd E (y i), ?_, ?_⟩
  · intro h
    apply hy
    ext i
    have h1 := congrFun h i
    simpa using h1
  · ext j
    have h1 := hcon (Pi.single j 1)
    rw [hform_eq] at h1
    simpa [Matrix.vecMul, dotProduct, Pi.single_apply] using h1

end Lemmas

end PI.NormGramAtOrigin.UnitaryGroupMassFormula
