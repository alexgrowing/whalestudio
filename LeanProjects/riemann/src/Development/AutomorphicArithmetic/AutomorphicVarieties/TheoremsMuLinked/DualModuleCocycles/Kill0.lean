import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem k0 {O G : Type} [CommRing O] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) O) (c₀ : O)
    (hs : ∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) (X : Type) [CommRing X] [Algebra O X]
    (W : Matrix (Fin n) (Fin n) X) (h : ∀ g, (bar X (ρ g) * W).trace = 0) : c₀ • W = 0 := by
  have key : ∀ M ∈ Submodule.span O (Set.range ρ), (bar X M * W).trace = 0 := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact h g
    | zero => simp [bar]
    | add x y _ _ hx hy =>
      have e : bar X (x + y) = bar X x + bar X y := by
        ext i j
        simp [bar]
      rw [e, add_mul, Matrix.trace_add, hx, hy, add_zero]
    | smul a x _ hx =>
      have e : bar X (a • x) = a • bar X x := by
        ext i j
        simp only [bar]
        rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul,
          Algebra.smul_def]
      rw [e, Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
  ext i j
  have t := key _ (hs (Matrix.single j i 1))
  have e : bar X (c₀ • Matrix.single j i (1 : O)) = Matrix.single j i (algebraMap O X c₀) := by
    ext a b
    simp [bar, Matrix.single_apply]
    split_ifs <;> simp
  rw [e] at t
  simpa [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Algebra.smul_def] using t

theorem UpperTheory.V.Th.Coc.kill0 :
    ∀ {O G : Type} [CommRing O] [IsDomain O] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) O) (c₀ : O), c₀ ≠ 0 → (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → (∀ W : Matrix (Fin n) (Fin n) O, (∀ g, (ρ g * W).trace = 0) → W = 0) ∧ ∀ (X : Type) [CommRing X] [Algebra O X] (W : Matrix (Fin n) (Fin n) X), (∀ g, (bar X (ρ g) * W).trace = 0) → c₀ • W = 0 := by
  intro O G _ _ _ n ρ c₀ hc hs
  refine ⟨fun W hW => ?_, fun X _ _ W hW => k0 ρ c₀ hs X W hW⟩
  have hb : ∀ g, (bar O (ρ g) * W).trace = 0 := by
    intro g
    have e : bar O (ρ g) = ρ g := by
      ext i j
      simp [bar]
    rw [e]
    exact hW g
  have := k0 ρ c₀ hs O W hb
  ext i j
  have := congrFun (congrFun this i) j
  simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at this
  exact (mul_eq_zero.mp this).resolve_left hc
