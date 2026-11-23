import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OfRealVecHalfVec

noncomputable section

open Complex Matrix ReciprocityTheory.PTheta

namespace ReciprocityTheory.ChartRestriction.G.Key.Chi

theorem chiU_mul {g : ℕ} {x y : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hx : x ∈ Matrix.symplecticGroup (Fin g) ℤ) (hy : y ∈ Matrix.symplecticGroup (Fin g) ℤ)
    (Hx : ChiAtU g x) (Hy : ChiAtU g y) : ChiAtU g (x * y) := by
  intro n n'
  obtain ⟨k, k', c, hc, H⟩ := Hy n n'
  obtain ⟨m, m', c', hc', H'⟩ := Hx k k'
  refine ⟨m, m', c' * c, by rw [mul_pow, hc, hc', one_mul], ?_⟩
  intro τ hτ z
  obtain ⟨hj, hs⟩ := spAct_holds g y hy τ hτ
  have hj' := (spAct_holds g x hx _ hs).1
  have hA := sp_A hy hτ.1 hj
  rw [zAct_mul x y τ hj, spAct_mul x y τ hj, H' _ hs, H τ hτ z, det_jAut_mul x y τ hj,
    expArg_mul x y τ hj hj' hA, eC_add]
  ring

theorem one_eq_spTransl_zero (g : ℕ) :
    (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) = spTransl 0 := by
  exact Matrix.fromBlocks_one.symm

theorem chiU_closure {g : ℕ} (hInv : InversionStatement)
    {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} (hγ : γ ∈ Submonoid.closure (spGens g)) :
    γ ∈ Matrix.symplecticGroup (Fin g) ℤ ∧ ChiAtU g γ := by
  induction hγ using Submonoid.closure_induction with
  | mem x hx => exact ⟨spGens_subset g hx, chiU_gen hInv hx⟩
  | one =>
    refine ⟨one_mem _, ?_⟩
    rw [one_eq_spTransl_zero]
    exact chiU_spTransl 0 Matrix.isSymm_zero
  | mul x y _ _ hx hy => exact ⟨mul_mem hx.1 hy.1, chiU_mul hx.1 hy.1 hx.2 hy.2⟩

theorem chi_of (hInv : InversionStatement) (hGen : SpGenStatement) : ChiStatement :=
  fun g γ hγ => chiAt_of_U (chiU_closure hInv (hGen g γ hγ)).2

end ReciprocityTheory.ChartRestriction.G.Key.Chi
