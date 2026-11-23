import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
open UpperTheory.Gal.Gen

open Classical in
private noncomputable def rho0 (H : Type) [Group H] [Fintype H] : H →* Matrix H H ℤ where
  toFun u := Matrix.of fun h g => if h = u * g then 1 else 0
  map_one' := by
    ext h g
    simp [Matrix.one_apply]
  map_mul' u v := by
    ext h g
    have e : ∀ x, (if h = u * x then (1 : ℤ) else 0) * (if x = v * g then 1 else 0)
        = if x = v * g then (if h = u * x then 1 else 0) else 0 := by
      intro x
      split_ifs <;> simp
    simp only [Matrix.mul_apply, Matrix.of_apply, e, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      mul_assoc]

theorem UpperTheory.Gal.Gen.groupDet_pf :
    UpperTheory.Gal.Gen.TriMat → UpperTheory.Gal.Gen.DetLow → UpperTheory.Gal.Gen.GroupDet := by
  classical
  intro hT hD k _ _ l _ H _ _ hp a ρ ha hrank
  obtain ⟨Q, P, hQP⟩ := hT l H hp H (rho0 H)
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix H H k, A = Matrix.of fun h g : H => a (h * g⁻¹) := ⟨_, rfl⟩
  rw [← hAdef] at hrank
  obtain ⟨R, hR⟩ : ∃ R : H → Matrix (Fin (Fintype.card H)) (Fin (Fintype.card H)) ℤ,
      R = fun u => Q * rho0 H u * P := ⟨_, rfl⟩
  have hm : ∀ u i j, ∃ m : ℤ, j ≤ i → R u i j - (if i = j then 1 else 0) = (l : ℤ) * m := by
    intro u i j
    by_cases h : j ≤ i
    · obtain ⟨m, hm⟩ := hQP u i j h
      exact ⟨m, fun _ => by rw [hR]; exact hm⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose m hm using hm
  have hAsum : A = ∑ u, a u • (rho0 H u).map (Int.castRingHom k) := by
    ext h g
    have e : ∀ u : H, h = u * g ↔ u = h * g⁻¹ := fun u => by
      constructor
      · rintro rfl; simp
      · rintro rfl; simp
    simp [hAdef, Matrix.sum_apply, rho0, e]
  obtain ⟨A', hA'def⟩ : ∃ A' : Matrix (Fin (Fintype.card H)) (Fin (Fintype.card H)) k,
      A' = Q.map (Int.castRingHom k) * A * P.map (Int.castRingHom k) := ⟨_, rfl⟩
  have hA'sum : A' = ∑ u, a u • (R u).map (Int.castRingHom k) := by
    rw [hA'def, hAsum, hR]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul]
  have hA' : ∀ i j, A' i j = ∑ u, a u * ((R u i j : ℤ) : k) := by
    intro i j
    rw [hA'sum]
    simp [Matrix.sum_apply]
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin (Fintype.card H)) (Fin (Fintype.card H)) k,
      B = Matrix.of fun i j => - ∑ u, a u * ((m u i j : ℤ) : k) := ⟨_, rfl⟩
  have hTe : ∀ i j, j ≤ i → (A' + (l : k) • B) i j = (∑ u, a u) * (if i = j then 1 else 0) := by
    intro i j hij
    have e : ∀ u, ((R u i j : ℤ) : k) = (if i = j then 1 else 0) + (l : k) * ((m u i j : ℤ) : k) := by
      intro u
      have := hm u i j hij
      have h2 : R u i j = (if i = j then 1 else 0) + (l : ℤ) * m u i j := by linarith
      rw [h2]
      push_cast
      rfl
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hA', hB, Matrix.of_apply, e,
      mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
    have : ∀ u, a u * ((l : k) * ((m u i j : ℤ) : k)) = (l : k) * (a u * ((m u i j : ℤ) : k)) :=
      fun u => by ring
    simp only [this]
    simp
  have hdet : (A' + (l : k) • B).det = (∑ u, a u) ^ Fintype.card H := by
    rw [Matrix.det_of_upperTriangular]
    · simp [hTe]
    · intro i j hij
      have hji : j < i := hij
      rw [hTe i j hji.le, if_neg hji.ne', mul_zero]
  have hnA : ∀ i j, ‖A' i j‖ ≤ 1 := by
    intro i j
    rw [hA']
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun u _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (ha u) (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one k _)
  have hnB : ∀ i j, ‖B i j‖ ≤ 1 := by
    intro i j
    rw [hB, Matrix.of_apply, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun u _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (ha u) (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one k _)
  have hnl : ‖(l : k)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one k l
  have hr : A'.rank ≤ ρ := by
    rw [hA'def]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hrank)
  have := hD k (Fintype.card H) A' B (l : k) ρ hnA hnB hnl hr
  rw [hdet, norm_pow] at this
  exact this
