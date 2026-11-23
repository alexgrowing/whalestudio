import Formalism.HermitianCurvature.HermitianCurvatureProofs.CardInsertEmbedding

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

namespace DeterminantReindex

open C2x2 CardInsertEmbedding

lemma perm_of_range {m k : ℕ} (e ρ : Fin k → Fin m) (he : Function.Injective e)
    (hr : ∀ t, ∃ s, ρ s = e t) : ∃ τ : Equiv.Perm (Fin k), ∀ t, e t = ρ (τ t) := by
  choose τ' hτ' using hr
  have hinj : Function.Injective τ' := by
    intro x y hxy; apply he; rw [← hτ' x, ← hτ' y, hxy]
  refine ⟨Equiv.ofBijective τ' (Finite.injective_iff_bijective.mp hinj), fun t => ?_⟩
  simp [hτ']

lemma det_reindex {m k : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (e ρ f : Fin k → Fin m) (τ : Equiv.Perm (Fin k))
    (h : ∀ t, e t = ρ (τ t)) :
    (M.submatrix e f).det = ((Equiv.Perm.sign τ : ℤ) : ℂ) * (M.submatrix ρ f).det := by
  have : M.submatrix e f = (M.submatrix ρ f).submatrix τ id := by
    ext t s; simp [h]
  rw [this, Matrix.det_permute]

lemma sign_sq {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    ((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simp

lemma sign_pm {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    ((Equiv.Perm.sign τ : ℤ) : ℂ) = 1 ∨ ((Equiv.Perm.sign τ : ℤ) : ℂ) = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simp

lemma U_mul_sub {m k : ℕ} (hkm : k ≤ m) (M U : Matrix (Fin m) (Fin m) ℂ) (hU : ∀ i j, j < i → U i j = 0)
    (e f : Fin k → Fin m) (hf : ∀ t, (f t).val = t.val) :
    (M * U).submatrix e f = M.submatrix e f * U.submatrix f f := by
  ext t s
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [sum_emb hkm f hf]
  intro j hj
  rw [hU _ _ (by rw [Fin.lt_def, hf]; omega), mul_zero]

lemma submatrix_mul_monomialMatrix {m k : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (M : Matrix (Fin m) (Fin m) ℂ)
    (e f : Fin k → Fin m) :
    (M * C2.monoP w d).submatrix e f = M.submatrix e (fun s => w (f s)) * Matrix.diagonal (fun s => d (f s)) := by
  ext t s
  rw [Matrix.mul_diagonal]
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, C2.monoP, Matrix.of_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma prod_emb {m k n : ℕ} (hkn : k = n) (d : Fin m → ℂ) (e : Fin k → Fin m) (he : ∀ t, (e t).val = t.val) :
    ∏ t, d (e t) = ∏ j ∈ Finset.range n, (if h : j < m then d ⟨j, h⟩ else 1) := by
  subst hkn
  rw [← Fin.prod_univ_eq_prod_range (fun j => if h : j < m then d ⟨j, h⟩ else 1)]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  have hlt : t.val < m := by have := (e t).isLt; rw [he] at this; exact this
  rw [dif_pos hlt]; congr 1; exact Fin.ext (he t)

end DeterminantReindex

end Formalism.FourierDecayAlt.P
