import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.hasModerateGrowth_constantTerm :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ), HasModerateGrowth φ → HasModerateGrowth (constantTerm r φ) := by
  intro K _ _ n r φ ⟨C, N, hφ⟩
  obtain ⟨D, hD, hsub⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  obtain ⟨M, hM⟩ := CuspidalSpectrum.exists_height_le_of_isCompact (hD.image continuous_unipGL)
  have hc0 : 0 ≤ heightConst K n := le_trans zero_le_one one_le_heightConst
  have hfin : unipMeasure K n r (unipFundamentalDomain K n r) < ⊤ :=
    (measure_mono hsub).trans_lt hD.measure_lt_top
  refine ⟨|C| * (heightConst K n * |M|) ^ N * (unipMeasure K n r).real (unipFundamentalDomain K n r), N, fun g => ?_⟩
  have hg := (height_pos g).le
  have hb : ∀ X ∈ unipFundamentalDomain K n r,
      ‖φ (unipGL X * g)‖ ≤ |C| * (heightConst K n * |M| * AutomorphicForm.height g) ^ N := by
    intro X hX
    have h1 : AutomorphicForm.height (unipGL X * g) ≤ heightConst K n * |M| * AutomorphicForm.height g :=
      (height_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((hM _ ⟨X, hsub hX, rfl⟩).trans (le_abs_self M)) hc0) hg)
    exact (hφ _).trans (mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (height_pos _).le h1 N)
      (pow_nonneg (height_pos _).le N) (abs_nonneg C))
  refine (norm_setIntegral_le_of_norm_le_const hfin hb).trans (le_of_eq ?_)
  rw [mul_pow (heightConst K n * |M|)]
  ring
