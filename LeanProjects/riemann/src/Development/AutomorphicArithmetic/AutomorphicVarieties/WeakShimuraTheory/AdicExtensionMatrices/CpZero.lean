import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def cpZeroPol {Λ A : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] (𝒜 : ℤ × ℤ → Submodule Λ A)
    (w : ℤ × ℤ) : AddSubgroup A[X] where
  carrier := {p | ∀ n, p.coeff n ∈ 𝒜 w}
  add_mem' := fun {p q} hp hq n => by rw [coeff_add]; exact add_mem (hp n) (hq n)
  zero_mem' := fun n => by rw [coeff_zero]; exact zero_mem _
  neg_mem' := fun {p} hp n => by rw [coeff_neg]; exact neg_mem (hp n)

private theorem cpZeroPol_graded {Λ A : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] (𝒜 : ℤ × ℤ → Submodule Λ A)
    [SetLike.GradedMonoid 𝒜] : SetLike.GradedMonoid (cpZeroPol 𝒜) where
  one_mem := fun n => by
    rw [coeff_one]
    split_ifs
    · exact SetLike.one_mem_graded 𝒜
    · exact zero_mem _
  mul_mem := fun i j p q hp hq n => by
    rw [coeff_mul]
    exact Submodule.sum_mem _ fun x _ => SetLike.mul_mem_graded (hp x.1) (hq x.2)

theorem UpperTheory.V.Ws.sxCpZero :
    ∀ {Λ A : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] (𝒜 : ℤ × ℤ → Submodule Λ A) [SetLike.GradedMonoid 𝒜] (M : M4 A), (∀ i j, M i j ∈ 𝒜 (wt i j)) → ∀ n, M.charpoly.coeff n ∈ 𝒜 0 := by
  intro Λ A _ _ _ 𝒜 _ M hM
  haveI := cpZeroPol_graded 𝒜
  have hC : ∀ i j, C (M i j) ∈ cpZeroPol 𝒜 (wt i j) := fun i j n => by
    rw [coeff_C]
    split_ifs
    · exact hM i j
    · exact zero_mem _
  have hX : (X : A[X]) ∈ cpZeroPol 𝒜 0 := fun n => by
    rw [coeff_X]
    split_ifs
    · exact SetLike.one_mem_graded 𝒜
    · exact zero_mem _
  have hE : ∀ i j, M.charmatrix i j ∈ cpZeroPol 𝒜 (wt i j) := by
    intro i j
    by_cases h : i = j
    · subst h
      rw [Matrix.charmatrix_apply_eq]
      refine sub_mem ?_ (hC i i)
      have : wt i i = 0 := by simp [wt]
      rw [this]; exact hX
    · rw [Matrix.charmatrix_apply_ne _ _ _ h]
      exact neg_mem (hC i j)
  have key : M.charpoly ∈ cpZeroPol 𝒜 0 := by
    rw [Matrix.charpoly, Matrix.det_apply]
    refine AddSubgroup.sum_mem _ fun σ _ => ?_
    have h0 : ∑ i, wt (σ i) i = 0 := by
      have h1 := Equiv.sum_comp σ lamW
      have h2 := Equiv.sum_comp σ muW
      ext
      · simp only [wt, Prod.fst_sum, Finset.sum_sub_distrib, h1, sub_self, Prod.fst_zero]
      · simp only [wt, Prod.snd_sum, Finset.sum_sub_distrib, h2, sub_self, Prod.snd_zero]
    have hp : ∏ i, M.charmatrix (σ i) i ∈ cpZeroPol 𝒜 (∑ i, wt (σ i) i) :=
      SetLike.prod_mem_graded (cpZeroPol 𝒜) (fun i => wt (σ i) i) (fun i => M.charmatrix (σ i) i) fun i _ => hE (σ i) i
    rw [h0] at hp
    rw [Units.smul_def]
    exact AddSubgroup.zsmul_mem _ hp _
  exact key
