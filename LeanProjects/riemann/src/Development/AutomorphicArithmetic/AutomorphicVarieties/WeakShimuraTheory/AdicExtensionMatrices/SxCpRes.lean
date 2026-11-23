import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem cp_low {R : Type} [CommRing R] (M : M4 R) (σ : Equiv.Perm (Fin 4))
    (h : ∀ i j, i < j → M (σ i) (σ j) = 0) : M.charpoly = ∏ i, (X - C (M i i)) := by
  have h1 : (Matrix.reindex σ.symm σ.symm M).charpoly = M.charpoly := Matrix.charpoly_reindex _ _
  rw [← h1, ← Matrix.charpoly_transpose, Matrix.charpoly_of_upperTriangular]
  · simpa using Equiv.prod_comp σ fun i => X - C (M i i)
  · intro i j hij
    simpa using h j i hij

theorem UpperTheory.V.Ws.sxCpRes :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {R : Type} [CommRing R] (a : O →+* R) (P : PD Φ.ι Γ R), Φ.Res a P → ∀ g, (P.r g).charpoly = ∏ i, (X - C (a (Φ.χ i g))) := by
  intro O Γ _ _ Φ R _ a P h g
  simp only [← h.diag g]
  rcases h.shape with ⟨h1, -⟩ | h1
  · refine cp_low _ (Equiv.swap 1 2) fun i j hij => h1 g _ _ ?_ ?_
    · exact fun e => hij.ne ((Equiv.swap 1 2).injective e)
    · revert i j; decide
  · refine cp_low _ 1 fun i j hij => h1 g _ _ hij.ne ?_
    revert i j; decide
