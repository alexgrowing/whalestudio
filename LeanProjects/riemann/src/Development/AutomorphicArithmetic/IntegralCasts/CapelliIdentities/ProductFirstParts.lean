import Mathlib

noncomputable def UpperTheory.Reformulated.B.product_first_partition.blockEmb.{u_1, u_2} :
    (K : Type u_1) →
      [inst : CommRing K] →
        {S : Type u_2} → {k n : ℕ} → S → MvPolynomial (Fin k × Fin n) K →ₐ[K] MvPolynomial (S × Fin k × Fin n) K :=
    fun (K : Type u_1) [CommRing K] {S : Type u_2} {k n : ℕ} (s : S) ↦ MvPolynomial.rename fun (v : Fin k × Fin n) ↦ (s, v)

noncomputable def UpperTheory.Reformulated.B.product_first_partition.tensorLat.{u_1, u_2, u_3} :
    (R : Type u_1) →
      (K : Type u_2) →
        [inst : CommRing R] →
          [inst_1 : CommRing K] →
            [inst_2 : Algebra R K] →
              {S : Type u_3} →
                [Fintype S] →
                  {k n : ℕ} →
                    (S → Submodule R (MvPolynomial (Fin k × Fin n) K)) → Submodule R (MvPolynomial (S × Fin k × Fin n) K) :=
    fun (R : Type u_1) (K : Type u_2) [CommRing R] [CommRing K] [Algebra R K] {S : Type u_3} [Fintype S] {k n : ℕ}
        (M : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) ↦
      Submodule.span R
        {P : MvPolynomial (S × Fin k × Fin n) K |
          ∃ (F : S → MvPolynomial (Fin k × Fin n) K),
            (∀ (s : S), F s ∈ M s) ∧
              P =
                ∏ s : S,
                  (UpperTheory.Reformulated.B.product_first_partition.blockEmb K s : MvPolynomial (Fin k × Fin n) K → MvPolynomial (S × Fin k × Fin n) K)
                    (F s)}

private theorem UpperTheory.Reformulated.B.product_first_partition.span_mul_eq {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (M N : Submodule R A) :
    Submodule.span R {X : A | ∃ F ∈ M, ∃ G ∈ N, X = F * G} = M * N := by
  rw [Submodule.mul_def]
  congr 1
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_mul, SetLike.mem_coe, eq_comm]

private theorem UpperTheory.Reformulated.B.product_first_partition.tensorLat_eq {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}
    (N : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) :
    UpperTheory.Reformulated.B.product_first_partition.tensorLat R K N =
      ∏ s : S, (N s).map ((UpperTheory.Reformulated.B.product_first_partition.blockEmb K s).restrictScalars R).toLinearMap := by
  have h : ∀ s : S, (N s).map ((UpperTheory.Reformulated.B.product_first_partition.blockEmb K s).restrictScalars R).toLinearMap =
      Submodule.span R (((N s).map
        ((UpperTheory.Reformulated.B.product_first_partition.blockEmb K s).restrictScalars R).toLinearMap : Submodule R _) : Set _) :=
    fun s => (Submodule.span_eq _).symm
  rw [Finset.prod_congr rfl fun s _ => h s, Submodule.prod_span]
  unfold UpperTheory.Reformulated.B.product_first_partition.tensorLat
  congr 1
  ext P
  rw [Set.mem_fintype_prod]
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨fun s => UpperTheory.Reformulated.B.product_first_partition.blockEmb K s (F s), fun s => ⟨F s, hF s, rfl⟩, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    choose F hF hFg using hg
    exact ⟨F, hF, Finset.prod_congr rfl fun s _ => (hFg s).symm⟩

theorem UpperTheory.Reformulated.B.product_first_partition.tensor_onto :
    ∀ {R K : Type} [inst : CommRing R] [inst_1 : Field K] [inst_2 : Algebra R K] {S : Type} [inst_3 : Fintype S]
      [DecidableEq S] {k n : ℕ} (A B M : S → Submodule R (MvPolynomial (Fin k × Fin n) K)),
      (∀ (s : S), M s ≤ Submodule.span R {X : MvPolynomial (Fin k × Fin n) K | ∃ F ∈ A s, ∃ G ∈ B s, X = F * G}) →
        UpperTheory.Reformulated.B.product_first_partition.tensorLat R K M ≤
          Submodule.span R
            {X : MvPolynomial (S × Fin k × Fin n) K |
              ∃ P ∈ UpperTheory.Reformulated.B.product_first_partition.tensorLat R K A, ∃ Q ∈ UpperTheory.Reformulated.B.product_first_partition.tensorLat R K B, X = P * Q} := by
  intro R K _ _ _ S _ _ k n A B M h
  rw [UpperTheory.Reformulated.B.product_first_partition.span_mul_eq, UpperTheory.Reformulated.B.product_first_partition.tensorLat_eq, UpperTheory.Reformulated.B.product_first_partition.tensorLat_eq,
    UpperTheory.Reformulated.B.product_first_partition.tensorLat_eq, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun s _ => ?_
  rw [← Submodule.map_mul]
  refine Submodule.map_mono ?_
  rw [← UpperTheory.Reformulated.B.product_first_partition.span_mul_eq]
  exact h s
