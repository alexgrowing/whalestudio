import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ScalarComm

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem cyc {K : Type} [Field K] {τ : K} (hτ : τ ^ 2 - 4 ≠ 0) (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (hj : (j ω).trace = τ) :
    ∃ g : GL (Fin 2) K, j ω * g = g * !![0, -1; 1, τ] := by
  have hd := j_det_omega j hj
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.trace_fin_two] at hj
  by_cases hc : j ω 1 0 ≠ 0
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, j ω 0 0; 0, j ω 1 0]
      (by simpa [Matrix.det_fin_two] using hc), ?_⟩
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | ring1 | linear_combination (j ω 0 0) * hj - hd | linear_combination (j ω 1 0) * hj | linear_combination (j ω 0 1) * hj | linear_combination (j ω 1 1) * hj - hd
  · push_neg at hc
    by_cases hb : j ω 0 1 ≠ 0
    · simp only [hc, mul_zero, sub_zero] at hd
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, j ω 0 1; 1, j ω 1 1]
        (by simpa [Matrix.det_fin_two] using hb), ?_⟩
      rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      ext i k
      fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc] <;> first | ring1 | linear_combination (j ω 0 0) * hj - hd | linear_combination (j ω 1 0) * hj | linear_combination (j ω 0 1) * hj | linear_combination (j ω 1 1) * hj - hd
    · push_neg at hb
      simp only [hb, hc, mul_zero, sub_zero] at hd
      have hne : j ω 1 1 - j ω 0 0 ≠ 0 := by
        intro h; apply hτ; rw [← hj]
        linear_combination (j ω 1 1 - j ω 0 0) * h + 4 * hd
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, j ω 0 0; 1, j ω 1 1]
        (by simpa [Matrix.det_fin_two] using hne), ?_⟩
      rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      ext i k
      fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb, hc] <;> first | ring1 | linear_combination (j ω 0 0) * hj - hd | linear_combination (j ω 1 0) * hj | linear_combination (j ω 0 1) * hj | linear_combination (j ω 1 1) * hj - hd

theorem UpperTheory.V.Z.Sym.Loc.gConj : UpperTheory.V.Z.Sym.Loc.GConj := by
  intro O K _ _ _ _ _ Δ τ hL hτ j j' hj hj'
  obtain ⟨g1, hg1⟩ := cyc hτ j hj
  obtain ⟨g2, hg2⟩ := cyc hτ j' hj'
  have e1 : ((g1⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j ω * g1 = !![0, -1; 1, τ] := by
    rw [mul_assoc, hg1, ← mul_assoc, Units.inv_mul, one_mul]
  have e2 : j' ω = (g2 : Matrix (Fin 2) (Fin 2) K) * !![0, -1; 1, τ] *
      ((g2⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    rw [← hg2, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin 2) K, g = g1 * g2⁻¹ := ⟨_, rfl⟩
  have hM : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j ω * g = j' ω := by
    rw [hg, e2, ← e1]; simp only [mul_inv_rev, inv_inv, Units.val_mul, mul_assoc]
  have hconj : ∀ z : (Etau K τ)ˣ, jU j' z = g⁻¹ * jU j z * g := by
    intro z; ext1
    simp only [jU, Units.coe_map, Units.val_mul, MonoidHom.coe_coe]
    rw [j_apply j', j_apply j, ← hM]
    simp [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
  refine ⟨⟨g, hconj⟩, fun χ hχ z => ?_⟩
  unfold gOrb
  refine orb_congr _ _ _ _ _ _ _ _ _ _ _ (Equiv.mulLeft g⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro t y; simp only [Equiv.coe_mulLeft]; rw [hconj t]; simp [mul_assoc]
  · intro y y'; simp [mul_assoc]
  · intro y; simp only [Equiv.coe_mulLeft, MonoidHom.id_apply]; rw [hconj z]; simp [mul_assoc]
  · intro y y' hyy
    simp only [MonoidHom.id_apply]
    rw [← fZK_conj hL hχ hyy]; congr 1; group
  · intro t; simp only [MonoidHom.id_apply]
    rw [← map_inv, ← map_mul, ← map_mul, mul_comm t⁻¹ z, mul_assoc, inv_mul_cancel, mul_one]
