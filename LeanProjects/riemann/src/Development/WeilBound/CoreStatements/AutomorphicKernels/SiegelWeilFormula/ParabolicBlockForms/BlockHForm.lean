import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.QE

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PositivityTheory.SiegelWeilFormula.Act.C4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} (L : LD d)

namespace Bq

private theorem QE_mul_apply_inl {n : ℕ} (ε : ℤˣ) (R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)
    (a : Fin n) (q : Fin n ⊕ Fin n) : ((QE n ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) * R) (Sum.inl a) q = R (Sum.inr a) q := by
  simp [QE, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, ite_mul, Finset.sum_ite_eq]

private theorem QE_mul_apply_inr {n : ℕ} (ε : ℤˣ) (R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)
    (a : Fin n) (q : Fin n ⊕ Fin n) : ((QE n ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) * R) (Sum.inr a) q = ((ε : ℤ) : E) * R (Sum.inl a) q := by
  simp [QE, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.smul_apply, smul_ite,
    smul_eq_mul, ite_mul, Finset.sum_ite_eq, mul_comm, mul_left_comm]

private theorem QE_emS_emS (ε : ℤˣ) (p q : Fin L.n ⊕ Fin L.n) :
    QE d.n ε (emS L p) (emS L q) = (QE L.n ε p q : E) := by
  rcases p with i | i <;> rcases q with k | k <;>
    simp [QE, emS, Matrix.one_apply, L.inj.eq_iff]

private theorem sum_sum_ne_eps_eq_plusIdx_minusIdx_add (f : Fin d.n → E) : ∑ a, f a = f L.i₀ + ∑ a', f (L.em a') := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ L.i₀)]
  congr 1
  have hs : Finset.univ.erase L.i₀ = Finset.univ.image L.em := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_image, true_and]
    rw [L.rng x]
    exact Set.mem_range
  rw [hs, Finset.sum_image fun x _ y _ h => L.inj h]

theorem blockH_form {ε : ℤˣ} {M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E}
    (hM : Mᵀ * QE d.n ε * M.map σ = QE d.n ε)
    (hx : ∀ r, M r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀))
    (hy : ∀ c, c ≠ Sum.inr L.i₀ → M (Sum.inr L.i₀) c = 0) :
    (M.submatrix (emS L) (emS L))ᵀ * QE L.n ε * (M.submatrix (emS L) (emS L)).map σ = QE L.n ε := by
  have hne : ∀ x : Fin L.n ⊕ Fin L.n, emS L x ≠ Sum.inr L.i₀ := by
    rintro (k | k) h
    · simp [emS] at h
    · simp only [emS, Sum.map_inr, Sum.inr.injEq] at h
      exact (L.rng (L.em k)).2 ⟨k, rfl⟩ h
  ext p q
  have key := congrFun (congrFun hM (emS L p)) (emS L q)
  rw [QE_emS_emS] at key
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type] at key ⊢
  simp only [Matrix.transpose_apply, QE_mul_apply_inl, QE_mul_apply_inr, Matrix.map_apply,
    Matrix.submatrix_apply] at key ⊢
  rw [sum_sum_ne_eps_eq_plusIdx_minusIdx_add L, sum_sum_ne_eps_eq_plusIdx_minusIdx_add L, hy _ (hne q), hy _ (hne p), map_zero] at key
  simp only [emS, Sum.map_inl, Sum.map_inr] at key ⊢
  linear_combination key

end Bq

end PositivityTheory.SiegelWeilFormula.Act.C4

end
