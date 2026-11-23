import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.DegreeHermitianFormula
open UpperTheory.V.Lit.Geo

private theorem absBd {V W F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [NormedAddCommGroup F] [NormedSpace ℝ F] (e : W ≃ₗ[ℝ] V) (q : ℕ) :
    ∃ (T : Finset (Fin q → W)) (B : ℝ), 0 ≤ B ∧ ∀ (m : MultilinearMap ℝ (fun _ : Fin q => W) F) (M : ℝ), 0 ≤ M →
      (∀ X ∈ T, ‖m X‖ ≤ M) → ∀ X, ‖m X‖ ≤ B * M * ∏ i, ‖e (X i)‖ := by
  classical
  let b := Module.finBasis ℝ V
  let c : Fin (Module.finrank ℝ V) → (V →L[ℝ] ℝ) := fun j => LinearMap.toContinuousLinearMap (b.coord j)
  refine ⟨Finset.univ.image fun I : Fin q → Fin (Module.finrank ℝ V) => fun i => e.symm (b (I i)),
    ∑ I : Fin q → Fin (Module.finrank ℝ V), ∏ i, ‖c (I i)‖, by positivity, fun m M hM hT X => ?_⟩
  have hX : X = fun i => ∑ j, c j (e (X i)) • e.symm (b j) := by
    funext i
    apply e.injective
    simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
    exact (b.sum_repr _).symm
  have h1 : m X = ∑ I : Fin q → Fin (Module.finrank ℝ V),
      (∏ i, c (I i) (e (X i))) • m fun i => e.symm (b (I i)) := by
    conv_lhs => rw [hX]
    rw [m.map_sum]
    exact Finset.sum_congr rfl fun I _ => m.map_smul_univ _ _
  rw [h1, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  rw [norm_smul, norm_prod, mul_right_comm, ← Finset.prod_mul_distrib]
  refine mul_le_mul (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => (c (I i)).le_opNorm _)
    (hT _ (Finset.mem_image_of_mem _ (Finset.mem_univ I))) (norm_nonneg _) (by positivity)

theorem UpperTheory.V.Lit.Geo.bdBasis :
    BdBasis := by
  intro E _ _ _ a Ξ q
  obtain ⟨T, B, hB, h⟩ := absBd (F := Fin Ξ.d → ℂ) (UpperTheory.V.Lit.Dr.hv (E := E) (a := a)) q
  refine ⟨T, B, hB, fun α g M hM hT X => ?_⟩
  exact h ((((LinearMap.proj _).comp UpperTheory.V.Lit.Dr.ev).restrictScalars ℝ).compMultilinearMap α.toMultilinearMap) M hM hT X
