import Mathlib

open Matrix Finset Equiv

namespace PI.IsoFunVW

theorem finite_oe (m n : ℕ) : Finite (Fin m ↪o Fin n) :=
  Finite.of_injective (fun e : Fin m ↪o Fin n => (e : Fin m → Fin n))
    (fun _ _ h => RelEmbedding.ext (congrFun h))

theorem det_mul_eq_sum_fun {R : Type*} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det = ∑ f : Fin m → Fin n, (∏ i, A i (f i)) * (B.submatrix f id).det := by
  have hdet : (A * B).det = (detRowAlternating : (Fin m → R) [⋀^Fin m]→ₗ[R] R)
      (fun (i : Fin m) => ∑ b : Fin n, A i b • (B b : Fin m → R)) := by
    rw [Matrix.det]; congr 1; ext i j; simp [Matrix.mul_apply, Finset.sum_apply]
  have hs := (detRowAlternating : (Fin m → R) [⋀^Fin m]→ₗ[R] R).toMultilinearMap.map_sum
    (fun (i : Fin m) (b : Fin n) => A i b • (B b : Fin m → R))
  rw [hdet]
  refine hs.trans (Finset.sum_congr rfl (fun f _ => ?_))
  have := (detRowAlternating : (Fin m → R) [⋀^Fin m]→ₗ[R] R).toMultilinearMap.map_smul_univ
    (fun i => A i (f i)) (fun i => (B (f i) : Fin m → R))
  refine this.trans ?_
  rw [smul_eq_mul]
  rfl

theorem det_submatrix_noninj {R : Type*} [CommRing R] {m n : ℕ}
    (B : Matrix (Fin n) (Fin m) R) (f : Fin m → Fin n) (hf : ¬ Function.Injective f) :
    (B.submatrix f id).det = 0 := by
  simp only [Function.Injective, not_forall] at hf
  obtain ⟨i, j, hij, hne⟩ := hf
  exact det_zero_of_row_eq hne (by ext k; simp [hij])

theorem det_mul_eq_sum_oe {R : Type*} [CommRing R] {m n : ℕ} [Fintype (Fin m ↪o Fin n)]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det = ∑ J : Fin m ↪o Fin n, (A.submatrix id J).det * (B.submatrix J id).det := by
  classical
  rw [det_mul_eq_sum_fun]
  set g : (Fin m → Fin n) → R := fun f => (∏ i, A i (f i)) * (B.submatrix f id).det with hg
  have h1 : ∑ f : Fin m → Fin n, g f =
      ∑ f ∈ univ.filter (fun f : Fin m → Fin n => Function.Injective f), g f := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    split_ifs with hf
    · rfl
    · simp [hg, det_submatrix_noninj B f hf]
  have h2 : ∀ J : Fin m ↪o Fin n, (A.submatrix id J).det * (B.submatrix J id).det
      = ∑ σ : Perm (Fin m), g (fun i => J (σ i)) := by
    intro J
    rw [← det_transpose (A.submatrix id J), det_apply', Finset.sum_mul]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    have hB : (B.submatrix (fun i => J (σ i)) id) = (B.submatrix J id).submatrix σ id := by
      ext i j; rfl
    simp only [hg, hB, det_permute]
    simp only [transpose_apply, submatrix_apply, id]
    ring
  rw [h1]
  simp_rw [h2]
  rw [← Fintype.sum_prod_type' (fun (J : Fin m ↪o Fin n) (σ : Perm (Fin m)) => g (fun i => J (σ i)))]
  symm
  refine Finset.sum_bij (fun p _ => fun i => p.1 (p.2 i)) ?_ ?_ ?_ ?_
  · intro p _
    simp only [mem_filter, mem_univ, true_and]
    exact p.1.injective.comp p.2.injective
  · intro p _ q _ h
    have hr : Set.range (p.1 : Fin m → Fin n) = Set.range (q.1 : Fin m → Fin n) := by
      have e1 : Set.range (fun i => p.1 (p.2 i)) = Set.range (p.1 : Fin m → Fin n) :=
        p.2.surjective.range_comp _
      have e2 : Set.range (fun i => q.1 (q.2 i)) = Set.range (q.1 : Fin m → Fin n) :=
        q.2.surjective.range_comp _
      rw [← e1, ← e2, h]
    have hJ : p.1 = q.1 :=
      RelEmbedding.ext (congrFun ((p.1.strictMono.range_inj q.1.strictMono).1 hr))
    have hσ : p.2 = q.2 := by
      ext i
      have := congrFun h i
      rw [hJ] at this
      exact congrArg Fin.val (q.1.injective this)
    exact Prod.ext hJ hσ
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    have hs : (univ.image f).card = m := by
      rw [card_image_of_injective _ hf, card_univ, Fintype.card_fin]
    set J := (univ.image f).orderEmbOfFin hs
    have hmem : ∀ i, ∃ k, J k = f i := by
      intro i
      have : f i ∈ Set.range J := by
        rw [Finset.range_orderEmbOfFin]; simp
      exact this
    choose τ hτ using hmem
    have hτi : Function.Injective τ := by
      intro a b hab
      apply hf
      rw [← hτ a, ← hτ b, hab]
    refine ⟨(J, Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτi)), mem_univ _, ?_⟩
    funext i
    simp [hτ]
  · intro p _
    rfl

end PI.IsoFunVW
