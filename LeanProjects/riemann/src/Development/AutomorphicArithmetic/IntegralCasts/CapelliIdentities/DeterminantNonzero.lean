import Mathlib

theorem UpperTheory.Reformulated.B.DeterminantNonzero.det_ne {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) (b : Module.Basis (Fin (m + 1)) F E) :
    (Matrix.of fun (i j : Fin (m + 1)) => (σ ^ (i : ℕ)) (b j)).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  have hord : orderOf σ = m + 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank, hm]
  have hinj : Function.Injective
      (fun i : Fin (m + 1) => ((σ ^ (i : ℕ) : E ≃ₐ[F] E) : E →ₐ[F] E)) := by
    intro i j hij
    have h1 : σ ^ (i : ℕ) = σ ^ (j : ℕ) := by
      ext x
      exact DFunLike.congr_fun hij x
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (by rw [hord]; exact i.2) (by rw [hord]; exact j.2) h1
  have hli := (linearIndependent_toLinearMap F E E).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  apply hv
  funext i
  refine hli v ?_ i
  apply b.ext
  intro j
  have := congrFun hvM j
  simpa [Matrix.vecMul, dotProduct, LinearMap.sum_apply] using this
