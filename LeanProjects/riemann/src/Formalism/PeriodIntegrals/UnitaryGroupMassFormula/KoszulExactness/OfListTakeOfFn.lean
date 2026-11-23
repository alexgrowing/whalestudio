import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.Ii

noncomputable section

universe u

namespace PI.KoszulExact

open RingTheory.Sequence

theorem ofList_take_ofFn {R : Type u} [CommRing R] {D : ℕ} (s : Fin D → R) (i : ℕ) :
    Ideal.ofList ((List.ofFn s).take i) = Ii s i := by
  unfold Ideal.ofList Ii
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_image]
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simp only [List.length_take, List.length_ofFn] at hj
    exact ⟨⟨j, by omega⟩, by simp only; omega, by simp⟩
  · rintro ⟨j, hj, rfl⟩
    have := j.isLt
    exact ⟨j, by simp only [List.length_take, List.length_ofFn]; omega, by simp⟩

theorem weak {R : Type u} [CommRing R] {D : ℕ} (s : Fin D → R)
    (hs : IsWeaklyRegular R (List.ofFn s)) (i : Fin D) (r : R) (hr : s i * r ∈ Ii s i) :
    r ∈ Ii s i := by
  have key := hs.regular_mod_prev i (by simp)
  have hsm : (Ideal.ofList ((List.ofFn s).take i) • ⊤ : Submodule R R) = Ii s i := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ofList_take_ofFn]
  have e : (List.ofFn s)[(i : ℕ)]'(by simp) = s i := by simp
  rw [e] at key
  have h1 : s i • (Submodule.Quotient.mk r :
      R ⧸ (Ideal.ofList ((List.ofFn s).take i) • ⊤ : Submodule R R)) = s i • 0 := by
    rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hsm, smul_eq_mul]
    exact hr
  have h2 := key h1
  rwa [Submodule.Quotient.mk_eq_zero, hsm] at h2

end PI.KoszulExact
