import Mathlib
open Matrix

namespace GlobalTheory.TraceGram

theorem pow_entry_mem {K : Type} [Field K] (O : Subring K) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K) (hg : ∀ i j, g i j ∈ O) (k : ℕ) : ∀ i j, (g ^ k) i j ∈ O := by
  induction k with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact O.sum_mem fun l _ => O.mul_mem (ih i l) (hg l j)

theorem adjugate_entry_mem {K : Type} [Field K] (O : Subring K) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (hG : ∀ i j, G i j ∈ O) : ∀ i j, G.adjugate i j ∈ O := by
  intro i j
  let G' : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨G i j, hG i j⟩
  have h : O.subtype.mapMatrix G' = G := by
    ext i j; rfl
  rw [← h, ← RingHom.map_adjugate]
  exact (G'.adjugate i j).2

theorem entry_mem_of_trace_gram : ∀ {K : Type} [Field K] (O : Subring K) {n : ℕ} (g x : Matrix (Fin n) (Fin n) K) (c : Fin n → K),
    x = ∑ i, c i • g ^ (i : ℕ) → (∀ i j, g i j ∈ O) → (∀ j : Fin n, (x * g ^ (j : ℕ)).trace ∈ O) →
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 →
    ((Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det)⁻¹ ∈ O → ∀ i j, x i j ∈ O := by
  intro K _ O n g x c hx hg htr hdet hinv
  set G : Matrix (Fin n) (Fin n) K := Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace with hGdef
  have hG : ∀ i j, G i j ∈ O := by
    intro i j
    simp only [hGdef, Matrix.of_apply, Matrix.trace, Matrix.diag_apply]
    exact O.sum_mem fun l _ => pow_entry_mem O g hg _ l l
  have hb : ∀ j, (c ᵥ* G) j ∈ O := by
    intro j
    have : (c ᵥ* G) j = (x * g ^ (j : ℕ)).trace := by
      rw [hx, Finset.sum_mul, Matrix.trace_sum]
      simp only [Matrix.vecMul, dotProduct, hGdef, Matrix.of_apply, smul_mul_assoc,
        Matrix.trace_smul, smul_eq_mul, pow_add]
    rw [this]; exact htr j
  have hc : ∀ i, c i ∈ O := by
    intro i
    have h1 : (c ᵥ* G) ᵥ* G.adjugate = G.det • c := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
    have h2 : c i = (G.det)⁻¹ * ((c ᵥ* G) ᵥ* G.adjugate) i := by
      rw [h1, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]
    rw [h2]
    refine O.mul_mem hinv ?_
    change ∑ l, (c ᵥ* G) l * G.adjugate l i ∈ O
    exact O.sum_mem fun l _ => O.mul_mem (hb l) (adjugate_entry_mem O G hG l i)
  intro i j
  rw [hx, Matrix.sum_apply]
  refine O.sum_mem fun l _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  exact O.mul_mem (hc l) (pow_entry_mem O g hg _ i j)

end GlobalTheory.TraceGram
