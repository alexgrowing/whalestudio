import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem ell_toL {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    ell E a (toL X) = (∑ w : InfinitePlace E, (X.trace w).re) / ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
  simp [ell, Matrix.trace, Finset.sum_apply]

private theorem ell_br {E : Type} [Field E] [NumberField E] {a : ℕ} (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    ell E a (toL (X * Y - Y * X)) = 0 := by
  rw [ell_toL, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  simp

theorem UpperTheory.V.Lit.Bor.ellFacts :
    UpperTheory.V.Lit.Bor.EllFacts := by
  intro E _ _ _ a
  refine ⟨fun ha => ?_, ell_br, fun k X => ?_, fun A _ _ _ _ L r hL X Y => ?_⟩
  · have h1 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
    have h2 : (Fintype.card (InfinitePlace E) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    change ell E a (toL 1) = 1
    rw [ell_toL, div_eq_one_iff_eq (mul_ne_zero h1 h2)]
    simp [mul_comm]
  · rw [ell_toL, ell_toL, Matrix.trace_mul_cycle, k.2.1, one_mul]
  · have h := hL X Y
    simp only [shift_apply, ell_br, mul_zero, zero_smul, add_zero, ← h, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, smul_add, smul_smul]
    rw [mul_comm (r * ell E a (toL Y))]
    abel
