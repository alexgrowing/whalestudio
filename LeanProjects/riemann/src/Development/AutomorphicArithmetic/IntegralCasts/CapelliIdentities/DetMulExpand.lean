import Mathlib

theorem UpperTheory.Reformulated.B.DetMulExpand.det_mul_expand :
    ∀ {F : Type} [inst : CommRing F] {k r : ℕ} (A : Matrix (Fin k) (Fin r) F) (B : Matrix (Fin r) (Fin k) F),
      (A * B).det = ∑ f : Fin k → Fin r, (∏ a : Fin k, A a (f a)) * (B.submatrix f id).det := by
  intro F _ k r A B
  have h1 : (A * B) = (fun a => ∑ j, (A a j • B j : Fin k → F)) := by
    ext a c
    simp [Matrix.mul_apply, Finset.sum_apply]
  have h2 : (A * B).det
      = (Matrix.detRowAlternating (R := F) (n := Fin k)).toMultilinearMap
          (fun a => ∑ j, (A a j • B j : Fin k → F)) := by
    rw [← h1]
    rfl
  rw [h2, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl
