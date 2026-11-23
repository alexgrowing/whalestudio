import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.liftOfS :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} {E : Type} [Ring E] [Algebra R E] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : E →+* Matrix (Fin n) (Fin n) O) (τ : E → R) (s : E →ₗ[R] Matrix (Fin n) (Fin n) R) (β : R) (b : O), IsDer x δ → (∀ (r : R) a, ρ (r • a) = x r • ρ a) → (∀ a, (ρ a).trace = x (τ a)) → x β = b → (∀ a a', s a * s a' = β • s (a * a')) → (∀ a, (s a).map x = b • ρ a) → (∀ a, (s a).trace = β * τ a) → ∃ d : E →+ Matrix (Fin n) (Fin n) X, IsLift x δ ρ τ (b * b) d := by
  intro O R X _ _ _ _ _ n E _ _ x δ ρ τ s β b hδ hρ htr hβ hs hx hst
  have hx' : ∀ a i j, x (s a i j) = b * ρ a i j := fun a i j => congrFun (congrFun (hx a) i) j
  have sm : ∀ (a : O) (y : X), a • y = algebraMap O X a * y := fun a y => Algebra.smul_def a y
  have en : ∀ a i j, (b • ((s a).map δ - δ β • bar X (ρ a))) i j =
      algebraMap O X b * (δ (s a i j) - δ β * algebraMap O X (ρ a i j)) := fun a i j => by
    rw [Matrix.smul_apply, sm]; rfl
  refine ⟨{ toFun := fun a => b • ((s a).map δ - δ β • bar X (ρ a))
            map_zero' := by ext i j; simp [bar]
            map_add' := fun a a' => by
              ext i j
              rw [Matrix.add_apply, en, en, en, map_add s, map_add ρ, Matrix.add_apply, Matrix.add_apply, map_add, map_add]
              ring }, fun a a' => ?_, fun r a => ?_, fun a => ?_⟩
  · ext i k
    have h1 := congrArg δ (congrFun (congrFun (hs a a') i) k)
    rw [Matrix.mul_apply, map_sum, Matrix.smul_apply, smul_eq_mul, hδ β, hβ, hx'] at h1
    simp only [hδ _ _, hx', sm, map_mul] at h1
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.add_apply, Matrix.mul_apply, en, Matrix.map_apply]
    rw [mul_sub, eq_sub_of_add_eq h1.symm]
    simp only [Matrix.mul_apply, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · ext i j
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.add_apply, en]
    rw [Matrix.smul_apply, en, Matrix.smul_apply, map_smul s, hρ, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, hδ r, hx']
    simp only [sm, map_mul, Matrix.map_apply]
    ring
  · have h1 : ((s a).map δ).trace = δ (s a).trace := by simp [Matrix.trace, map_sum]
    have h2 : (bar X (ρ a)).trace = algebraMap O X (ρ a).trace := by simp [bar, Matrix.trace, map_sum]
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.trace_smul, Matrix.trace_sub, h1, h2, hst, hδ _ _, hβ, htr]
    simp only [sm, map_mul, smul_eq_mul]
    ring
