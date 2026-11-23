import Mathlib

namespace UpperTheory.Reformulated.B.S3

private theorem prod_mul_mem {k : Type} [Field k] {n : ℕ} (W : Submodule k (Fin n → k)) (d : Fin n → k)
    (hW : ∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) (v : Fin n → k) (hv : v ∈ W) (s : Finset (Fin n)) :
    (fun j => (∏ l ∈ s, (d j - d l)) * v j) ∈ W := by
  induction s using Finset.induction_on with
  | empty => simpa using hv
  | insert a s ha ih =>
    have h := W.sub_mem (hW _ ih) (W.smul_mem (d a) ih)
    convert h using 1
    funext j
    simp only [Finset.prod_insert ha, Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_diagonal, smul_eq_mul]
    ring

theorem single_mem {k : Type} [Field k] {n : ℕ} (W : Submodule k (Fin n → k)) (d : Fin n → k) (hd : Function.Injective d)
    (hW : ∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) (v : Fin n → k) (hv : v ∈ W) (i : Fin n) (hi : v i ≠ 0) :
    (Pi.single i 1 : Fin n → k) ∈ W := by
  have h := prod_mul_mem W d hW v hv (Finset.univ.erase i)
  have hc : (∏ l ∈ Finset.univ.erase i, (d i - d l)) * v i ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun l hl => ?_) hi
    exact sub_ne_zero.mpr fun e => (Finset.ne_of_mem_erase hl) (hd e).symm
  have h2 := W.smul_mem ((∏ l ∈ Finset.univ.erase i, (d i - d l)) * v i)⁻¹ h
  convert h2 using 1
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hc]
  · have hz : (∏ l ∈ Finset.univ.erase i, (d j - d l)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) (sub_self _)
    rw [Pi.single_eq_of_ne hj, Pi.smul_apply, smul_eq_mul, hz, zero_mul, mul_zero]

end UpperTheory.Reformulated.B.S3
