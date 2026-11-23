import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
open GlobalTheory.WholeFlag GlobalTheory.WholeFlag.Glue
open scoped Matrix

set_option autoImplicit false

namespace GlobalTheory.WholeFlag.Glue

theorem minorAt_mul_upperTriangular {K : Type} [Field K] {n g : ℕ} (R : Matrix (Fin n) (Fin g) K)
    (T : Matrix (Fin g) (Fin g) K) (hT : T.BlockTriangular id) (k : ℕ) (hk : k ≤ g) (σ : Fin k → Fin n) :
    minorAt (R * T) k hk σ = minorAt R k hk σ * ∏ i : Fin k, T (Fin.castLE hk i) (Fin.castLE hk i) := by
  have hmat : (Matrix.of fun r l : Fin k => (R * T) (σ r) (Fin.castLE hk l)) =
      (Matrix.of fun r l : Fin k => R (σ r) (Fin.castLE hk l)) *
        (Matrix.of fun j l : Fin k => T (Fin.castLE hk j) (Fin.castLE hk l)) := by
    ext r l
    simp only [Matrix.mul_apply, Matrix.of_apply]
    symm
    have hm := Finset.sum_map Finset.univ (Fin.castLEEmb hk) (fun j : Fin g => R (σ r) j * T j (Fin.castLE hk l))
    refine Eq.trans (Eq.trans ?_ hm.symm) ?_
    · rfl
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hjk : k ≤ (j : ℕ) := by
      by_contra h
      push_neg at h
      exact hj (Finset.mem_map.2 ⟨⟨j, h⟩, Finset.mem_univ _, Fin.ext (by simp)⟩)
    have hlt : Fin.castLE hk l < j := by
      rw [Fin.lt_iff_val_lt_val]; simp; omega
    have h0 : T j (Fin.castLE hk l) = 0 := hT hlt
    simp only [h0, mul_zero]
  have htri : (Matrix.of fun j l : Fin k => T (Fin.castLE hk j) (Fin.castLE hk l)).BlockTriangular id := by
    intro i j hij
    simp only [Matrix.of_apply]
    apply hT
    rw [Fin.lt_iff_val_lt_val] at hij ⊢
    simpa using hij
  unfold minorAt
  rw [hmat, Matrix.det_mul, Matrix.det_of_upperTriangular htri]
  simp

end GlobalTheory.WholeFlag.Glue
