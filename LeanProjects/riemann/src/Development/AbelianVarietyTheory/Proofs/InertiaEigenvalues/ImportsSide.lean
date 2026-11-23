import Mathlib

namespace GlobalTheory.BasisMatrixExistence

theorem exists_basis {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {r : ℕ}
    (d : O) (hd : d ≠ 0) (N : Submodule O (Fin r → O)) (hN : ∀ x : Fin r → O, d • x ∈ N) :
    Nonempty (Module.Basis (Fin r) O N) := by
  classical
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin r)) N
  have : Module.Finite O N := Module.Finite.of_basis b
  have hfin : Module.finrank O N = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hle : n ≤ r := by
    have h := Submodule.finrank_le N
    rw [Module.finrank_fin_fun] at h
    omega

  let f : (Fin r → O) →ₗ[O] N :=
    { toFun := fun x => ⟨d • x, hN x⟩
      map_add' := fun x y => by ext1; simp [smul_add]
      map_smul' := fun c x => by ext1; simp [smul_comm d c x] }
  have hf : Function.Injective f := by
    intro x y hxy
    have h' : d • x = d • y := congrArg Subtype.val hxy
    exact smul_right_injective (Fin r → O) hd h'
  have hge : r ≤ n := by
    have h := LinearMap.finrank_le_finrank_of_injective hf
    rw [Module.finrank_fin_fun, hfin] at h
    exact h
  exact ⟨b.reindex (finCongr (le_antisymm hle hge))⟩

theorem exists_matrix {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {r : ℕ}
    (d : O) (hd : d ≠ 0) (N : Submodule O (Fin r → O)) (hN : ∀ x : Fin r → O, d • x ∈ N) :
    ∃ (G C : Matrix (Fin r) (Fin r) O), C * G = d • (1 : Matrix (Fin r) (Fin r) O) ∧
      ∀ v : Fin r → O, v ∈ N ↔ ∃ w : Fin r → O, v = Matrix.vecMul w G := by
  classical
  obtain ⟨b⟩ := exists_basis d hd N hN
  refine ⟨Matrix.of fun i j => (b i : Fin r → O) j,
    Matrix.of fun j i => b.repr ⟨d • Pi.single j 1, hN _⟩ i, ?_, ?_⟩
  · ext j k
    have hsum := congrArg (fun x : N => (x : Fin r → O) k) (b.sum_repr ⟨d • Pi.single j 1, hN _⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hsum
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [hsum]
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [Ne.symm hjk, hjk]
  · intro v
    constructor
    · intro hv
      refine ⟨fun i => b.repr ⟨v, hv⟩ i, ?_⟩
      have hsum := congrArg (fun x : N => (x : Fin r → O)) (b.sum_repr ⟨v, hv⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
      ext k
      have hk := congrFun hsum k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk
      rw [Matrix.vecMul, dotProduct]
      simp only [Matrix.of_apply]
      exact hk.symm
    · rintro ⟨w, rfl⟩
      have : Matrix.vecMul w (Matrix.of fun i j => (b i : Fin r → O) j) =
          ∑ i, w i • (b i : Fin r → O) := by
        ext k
        simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2

theorem main : (let d1 : {O : Type} → [inst : CommRing O] → (I : Ideal O) → (r : ℕ) → (Fin r → O) →ₗ[O] Fin r → O ⧸ I := @(fun {O : Type} [CommRing O] (I : Ideal O) (r : ℕ) ↦ LinearMap.compLeft (AlgHom.toLinearMap (Ideal.Quotient.mkₐ O I)) (Fin r)); ∀ {O : Type} [inst : CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {r : ℕ} (d : O), d ≠ (0 : O) → ∀ (l : Submodule O (Fin r → O ⧸ Ideal.span {d})), ∃ (G : Matrix (Fin r) (Fin r) O) (C : Matrix (Fin r) (Fin r) O), C * G = d • (1 : Matrix (Fin r) (Fin r) O) ∧ ∀ (v : Fin r → O), (d1 (Ideal.span {d}) r : (Fin r → O) → Fin r → O ⧸ Ideal.span {d}) v ∈ l ↔ ∃ (w : Fin r → O), v = Matrix.vecMul w G) := by
  intro d1 O _ _ _ r d hd l
  let N : Submodule O (Fin r → O) := l.comap (d1 (Ideal.span {d}) r)
  have hN : ∀ x : Fin r → O, d • x ∈ N := by
    intro x
    show d1 (Ideal.span {d}) r (d • x) ∈ l
    have h0 : d1 (Ideal.span {d}) r (d • x) = 0 := by
      ext i
      change Ideal.Quotient.mk (Ideal.span {d}) (d * x i) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self d)
    rw [h0]
    exact l.zero_mem
  obtain ⟨G, C, hCG, hG⟩ := exists_matrix d hd N hN
  exact ⟨G, C, hCG, fun v => hG v⟩

end GlobalTheory.BasisMatrixExistence
