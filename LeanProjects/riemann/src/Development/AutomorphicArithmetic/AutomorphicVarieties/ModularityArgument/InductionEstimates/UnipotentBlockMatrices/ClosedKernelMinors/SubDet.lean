import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem row_two {K : Type} [Field K] {n : ℕ} {w : InfinitePlace K} {k : GL (Fin n) w.Completion}
    (hk : k ∈ archCompact w) (i : Fin n) {a b : Fin n} (hab : a ≠ b) : ‖k i a‖ ^ 2 + ‖k i b‖ ^ 2 ≤ 1 := by
  classical
  have h := mem_archCompact.1 hk (Pi.single i 1)
  rw [Matrix.single_one_vecMul] at h
  have h1 : euclidNorm (Pi.single i (1 : w.Completion)) = 1 := by
    rw [euclidNorm, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp only [Pi.single_eq_same, norm_one, one_pow, Real.sqrt_one]
  rw [h1, euclidNorm, Real.sqrt_eq_one] at h
  rw [← h, ← Finset.sum_pair (f := fun j => ‖k i j‖ ^ 2) hab]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.subDet :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) (k : AdelicGLn.AdelicGL K n), k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) → ∀ (r c : Fin 2 → Fin n), Function.Injective r → Function.Injective c →
      (∀ w : InfinitePlace K, ‖(((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).1 w‖ ≤ 1) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ‖(((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).2 v‖ ≤ 1) ∧
      ∀ m : AdelicGLn.AdelicGL K 2, (m : Matrix (Fin 2) (Fin 2) 𝔸[K]) = (k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c → (detModule K 2 m).1 ≤ 1 := by
  intro K _ _ n k hk r c _ hc
  have hc01 : c 0 ≠ c 1 := fun h => absurd (hc h) (by decide)
  have H1 : ∀ w : InfinitePlace K, ‖(((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).1 w‖ ≤ 1 := by
    intro w
    have h0 := row_two ((mem_maxCompact.1 hk).1 w) (r 0) hc01
    have h1 := row_two ((mem_maxCompact.1 hk).1 w) (r 1) hc01
    have e : (((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).1 w =
        infAt w k (r 0) (c 0) * infAt w k (r 1) (c 1) - infAt w k (r 0) (c 1) * infAt w k (r 1) (c 0) := by
      rw [← infEval_apply, Matrix.det_fin_two, map_sub, map_mul, map_mul]
      rfl
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    nlinarith [sq_nonneg (‖infAt w k (r 0) (c 0)‖ - ‖infAt w k (r 1) (c 1)‖),
      sq_nonneg (‖infAt w k (r 0) (c 1)‖ - ‖infAt w k (r 1) (c 0)‖)]
  have H2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      ‖(((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).2 v‖ ≤ 1 := by
    intro v
    have hv := (mem_maxCompact.1 hk).2 v
    rw [GLnLocal.mem_integralGL_iff] at hv
    simp only [GroundTheory.Global.mem_valuationInteger_iff] at hv
    have e : (((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).2 v =
        finAt v k (r 0) (c 0) * finAt v k (r 1) (c 1) - finAt v k (r 0) (c 1) * finAt v k (r 1) (c 0) := by
      rw [← finEval_apply, Matrix.det_fin_two, map_sub, map_mul, map_mul]
      rfl
    rw [e]
    exact norm_le_one_of_mem v (sub_mem (mul_mem (hv.1 _ _) (hv.1 _ _)) (mul_mem (hv.1 _ _) (hv.1 _ _)))
  refine ⟨H1, H2, fun m hm => ?_⟩
  rw [← hm] at H1 H2
  change (GroundTheory.Global.IdeleGroup.ideleModule K (AdelicGLn.det K 2 m) : ℝ) ≤ 1
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  refine mul_le_one₀ (Finset.prod_le_one (fun _ _ => by positivity)
    fun w _ => pow_le_one₀ (norm_nonneg _) (H1 w)) (finprod_nonneg fun _ => norm_nonneg _) ?_
  exact finprod_induction (fun x : ℝ => 0 ≤ x ∧ x ≤ 1) ⟨zero_le_one, le_rfl⟩
    (fun x y hx hy => ⟨mul_nonneg hx.1 hy.1, mul_le_one₀ hx.2 hy.1 hy.2⟩)
    (fun v => ⟨norm_nonneg _, H2 v⟩) |>.2
