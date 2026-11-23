import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs

theorem UpperTheory.weilDeligne_monodromy_upperTriangular :
    UpperTheory.V.Af.Wd.TriMono := by
  intro k W Γ _ _ _ n N ρ c μ hcomm hT hN
  obtain ⟨b, hb⟩ := hT
  set B := LinearMap.toMatrix b b N with hBdef
  have hAlow : ∀ σ (i j : Fin n), j < i → LinearMap.toMatrix b b (ρ σ) i j = 0 := fun σ => (hb (some σ)).1
  have hAdiag : ∀ σ (i : Fin n), LinearMap.toMatrix b b (ρ σ) i i = μ σ i := fun σ => (hb (some σ)).2
  have hB0 : B ≠ 0 := by
    intro h
    apply hN
    apply (LinearMap.toMatrix b b).injective
    rw [← hBdef, h, map_zero]
  have hex : ∃ i j, B i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hB0 (Matrix.ext h)
  classical
  have hJ : (Finset.univ.filter fun j => ∃ i, B i j ≠ 0).Nonempty := by
    obtain ⟨i, j, h⟩ := hex
    exact ⟨j, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨i, h⟩⟩
  set j := (Finset.univ.filter fun j => ∃ i, B i j ≠ 0).min' hJ with hjdef
  have hjmem := Finset.min'_mem _ hJ
  rw [← hjdef] at hjmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjmem
  have hjmin : ∀ i l, l < j → B i l = 0 := by
    intro i l hl
    by_contra h
    have : j ≤ l := Finset.min'_le _ l (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨i, h⟩)
    exact absurd hl (not_lt.mpr this)
  have hI : (Finset.univ.filter fun i => B i j ≠ 0).Nonempty := by
    obtain ⟨i, h⟩ := hjmem
    exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h⟩
  set i := (Finset.univ.filter fun i => B i j ≠ 0).max' hI with hidef
  have himem := Finset.max'_mem _ hI
  rw [← hidef] at himem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at himem
  have himax : ∀ l, i < l → B l j = 0 := by
    intro l hl
    by_contra h
    have : l ≤ i := Finset.le_max' _ l (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
    exact absurd hl (not_lt.mpr this)
  refine ⟨i, j, fun σ => ?_⟩
  set A := LinearMap.toMatrix b b (ρ σ) with hAdef
  have hmat : A * B = c σ • (B * A) := by
    rw [hAdef, hBdef, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, ← map_smul, hcomm]
  have h1 : (A * B) i j = μ σ i * B i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hAdef, hAdiag]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hAdef, hAlow σ i l h, zero_mul]
      · rw [himax l h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h2 : (B * A) i j = B i j * μ σ j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j, hAdef, hAdiag]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hjmin i l h, zero_mul]
      · rw [hAdef, hAlow σ l j h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have h3 := congrFun (congrFun hmat i) j
  rw [Matrix.smul_apply, h1, h2, smul_eq_mul] at h3
  have : (μ σ i - c σ * μ σ j) * B i j = 0 := by rw [sub_mul, h3]; ring
  rcases mul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h himem
