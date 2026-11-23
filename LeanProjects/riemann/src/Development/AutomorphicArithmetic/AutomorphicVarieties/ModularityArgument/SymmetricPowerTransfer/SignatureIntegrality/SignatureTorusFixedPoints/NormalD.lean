import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryHyperbolicOrbitCount

open Matrix Polynomial GlobalTheory.SplitWeil GlobalTheory.SmGL

private theorem exists_eigvec {k : Type} [Field k] (M : Matrix (Fin 2) (Fin 2) k) (c : k)
    (h : M.charpoly.eval c = 0) : ∃ v : Fin 2 → k, v ≠ 0 ∧ M *ᵥ v = c • v := by
  rw [Matrix.eval_charpoly] at h
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec] at hMv
  have hs : Matrix.scalar (Fin 2) c *ᵥ v = c • v := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_smul]
  rw [hs] at hMv
  exact (sub_eq_zero.mp hMv).symm

theorem UpperTheory.V.Z.Sym.Sig.normalD :
    UpperTheory.V.Z.Sym.Sig.NormalD := by
  intro k _ _ _ _ γ a b hab hchar
  have ha : (γ : Matrix (Fin 2) (Fin 2) k).charpoly.eval (a : k) = 0 := by
    simp [hchar]
  have hb : (γ : Matrix (Fin 2) (Fin 2) k).charpoly.eval (b : k) = 0 := by
    simp [hchar]
  obtain ⟨v, hv0, hv⟩ := exists_eigvec _ _ ha
  obtain ⟨w, hw0, hw⟩ := exists_eigvec _ _ hb
  have hab' : (a : k) ≠ (b : k) := fun h => hab (Units.ext h)
  let P : Matrix (Fin 2) (Fin 2) k := Matrix.of fun i j => ![v, w] j i
  have hPv : ∀ u : Fin 2 → k, P *ᵥ u = u 0 • v + u 1 • w := by
    intro u
    ext i
    simp [P, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  have hdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [hPv] at hu
    have h2 : (γ : Matrix (Fin 2) (Fin 2) k) *ᵥ (u 0 • v + u 1 • w) = 0 := by
      rw [hu, Matrix.mulVec_zero]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hv, hw] at h2
    have h3 : (u 1 * ((b : k) - a)) • w = 0 := by
      have e : (u 1 * ((b : k) - a)) • w
          = (u 0 • (a : k) • v + u 1 • (b : k) • w) - (a : k) • (u 0 • v + u 1 • w) := by
        module
      rw [e, h2, hu, smul_zero, sub_zero]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · have hu1 : u 1 = 0 := by
        rcases mul_eq_zero.mp h4 with h5 | h5
        · exact h5
        · exact absurd (sub_eq_zero.mp h5).symm hab'
      rw [hu1, zero_smul, add_zero] at hu
      rcases smul_eq_zero.mp hu with h6 | h6
      · apply hu0
        ext i
        fin_cases i
        · simpa using h6
        · simpa using hu1
      · exact hv0 h6
    · exact hw0 h4
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P hdet, ?_⟩
  have hg : ((Matrix.GeneralLinearGroup.mkOfDetNeZero P hdet : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = P := rfl
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  simp only [Units.val_mul, hg, UpperTheory.V.Z.Sym.Sig.dg, val_diagT]
  ext i j
  fin_cases j
  · have := congrFun hv i
    simp [Matrix.mulVec, dotProduct] at this
    simp [P, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
    rw [this, mul_comm]
  · have := congrFun hw i
    simp [Matrix.mulVec, dotProduct] at this
    simp [P, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
    rw [this, mul_comm]
