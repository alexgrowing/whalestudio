import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PluckOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem hpq_loc {E : Type*} [NormedField E] {n : ℕ} (g : GL (Fin n) E) (i j p q : Fin n) :
    ‖(g : Matrix (Fin n) (Fin n) E) i j * (g : Matrix (Fin n) (Fin n) E) p q‖ ≤ locHeight g ^ 2 := by
  rw [norm_mul, sq]
  exact mul_le_mul (norm_apply_le_locHeight g i j) (norm_apply_le_locHeight g p q) (norm_nonneg _) (locHeight_pos g).le

private theorem hpq_minor {K : Type} [Field K] [NumberField K] {n : ℕ} (h : AdelicGLn.AdelicGL K n) (r c : Fin 2 → Fin n)
    (y : GroundTheory.Global.IdeleGroup K) (hy : (y : 𝔸[K]) = ((h : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det) :
    (GroundTheory.Global.IdeleGroup.ideleModule K y : ℝ) ≤ (∏ w : InfinitePlace K, (2 : ℝ) ^ w.mult) * AutomorphicForm.height h ^ 2 := by
  classical
  rw [Matrix.det_fin_two] at hy
  simp only [Matrix.submatrix_apply] at hy
  have hi : ∀ w : InfinitePlace K, ‖(y : 𝔸[K]).1 w‖ ≤ 2 * locHeight (infAt w h) ^ 2 := by
    intro w
    have e : (y : 𝔸[K]).1 w = (infAt w h : Matrix (Fin n) (Fin n) w.Completion) (r 0) (c 0) * (infAt w h : Matrix (Fin n) (Fin n) w.Completion) (r 1) (c 1) -
        (infAt w h : Matrix (Fin n) (Fin n) w.Completion) (r 0) (c 1) * (infAt w h : Matrix (Fin n) (Fin n) w.Completion) (r 1) (c 0) := by
      rw [hy]; rfl
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h1 := hpq_loc (infAt w h) (r 0) (c 0) (r 1) (c 1)
    have h2 := hpq_loc (infAt w h) (r 0) (c 1) (r 1) (c 0)
    linarith
  have hf : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ‖(y : 𝔸[K]).2 v‖ ≤ locHeight (finAt v h) ^ 2 := by
    intro v
    have e : (y : 𝔸[K]).2 v = (finAt v h : Matrix (Fin n) (Fin n) (v.adicCompletion K)) (r 0) (c 0) * (finAt v h : Matrix (Fin n) (Fin n) (v.adicCompletion K)) (r 1) (c 1) +
        -((finAt v h : Matrix (Fin n) (Fin n) (v.adicCompletion K)) (r 0) (c 1) * (finAt v h : Matrix (Fin n) (Fin n) (v.adicCompletion K)) (r 1) (c 0)) := by
      rw [hy, sub_eq_add_neg]; rfl
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hpq_loc _ _ _ _ _) ?_)
    rw [norm_neg]
    exact hpq_loc _ _ _ _ _
  set s := (finite_mulSupport_locHeight_finAt h).union (GroundTheory.Global.IdeleGroup.finite_mulSupport_norm y)
  have h1 : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), locHeight (finAt v h) = ∏ v ∈ s.toFinset, locHeight (finAt v h) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      simp only [Set.Finite.coe_toFinset, Set.mem_union]; exact Or.inl hv
  have h2 : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ‖(y : 𝔸[K]).2 v‖ = ∏ v ∈ s.toFinset, ‖(y : 𝔸[K]).2 v‖ :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      simp only [Set.Finite.coe_toFinset, Set.mem_union]; exact Or.inr hv
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, AutomorphicForm.height, h1, h2, mul_pow, ← mul_assoc, ← Finset.prod_pow, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  refine mul_le_mul (Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_)
    (Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => hf v) (Finset.prod_nonneg fun v _ => norm_nonneg _)
    (Finset.prod_nonneg fun w _ => by positivity)
  rw [← pow_mul, mul_comm w.mult 2, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hi w) _

private theorem hpq_rows {R : Type} [CommRing R] (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R)
    (c : Fin 2 → Fin (2 + 2)) :
    (((unipGL X * blk a b : GL (Fin (2 + 2)) R) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) * k).submatrix (Fin.natAdd 2) c =
      (b : Matrix (Fin 2) (Fin 2) R) * k.submatrix (Fin.natAdd 2) c := by
  have h1 : ∀ (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (i : Fin 2) j, (unipMatrix X * M) (Fin.natAdd 2 i) j = M (Fin.natAdd 2 i) j := by
    intro M i j
    have : (blockEntry X * M) (Fin.natAdd 2 i) j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [blockEntry_apply, dif_neg (by simp), zero_mul]
    rw [unipMatrix, add_mul, one_mul, Matrix.add_apply, this, add_zero]
  ext i j
  rw [Matrix.submatrix_apply, Units.val_mul, coe_unipGL, mul_assoc, h1, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_add]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.hpQht :
    ∀ {K : Type} [Field K] [NumberField K], ∃ c C : ℝ, 0 < c ∧ ∀ g : G1 K (2 + 2), HH g ≤ c * Real.log (qht g) + C := by
  intro K _ _
  set D : ℝ := (∏ w : InfinitePlace K, (2 : ℝ) ^ w.mult) * heightConst K (2 + 2) ^ 2 with hD
  have hc1 := one_le_heightConst (K := K) (n := 2 + 2)
  have hD0 : 0 < D := mul_pos (Finset.prod_pos fun w _ => by positivity) (by positivity)
  refine ⟨2, Real.log D, two_pos, fun g => ?_⟩
  obtain ⟨X, m₁, m₂, t, k, hk, hg⟩ := iwa g
  have ht : HH g = t := by
    rw [hg, (hpSpec (K := K)).1, ((hpSpec (K := K)).2.1 k hk).1, add_zero]
  have key : ∀ γ : Gam K (2 + 2), Real.exp t ≤
      D * AutomorphicForm.height (((γ : G1 K (2 + 2)) * g : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ^ 2 := by
    intro γ
    obtain ⟨δ, hδ⟩ : ∃ δ : GL (Fin (2 + 2)) K, AdelicGLn.diagonal K (2 + 2) δ = ((γ⁻¹ : Gam K (2 + 2)) : G1 K (2 + 2)) := (γ⁻¹).2
    set h : AdelicGLn.AdelicGL K (2 + 2) := (((γ : G1 K (2 + 2)) * g : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) with hh
    set b : AdelicGLn.AdelicGL K 2 := (m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t) with hb
    have hb' : (detModule K 2 b : ℝ) = Real.exp (-t) := by
      rw [hb, map_mul, mem_normOneGL_iff_detModule.1 m₂.2, one_mul, zt, detModule_centralSection two_pos]
    have e1 : AdelicGLn.diagonal K (2 + 2) δ =
        unipGL X * blk ((m₁ : AdelicGLn.AdelicGL K 2) * zt K t) b * ((k : AdelicGLn.AdelicGL K (2 + 2)) * h⁻¹) := by
      rw [← mul_assoc, hb, ← (blkLaws (K := K)).1, ← coe_unipOne, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← hg, hδ, hh]
      simp
    obtain ⟨c, -, hc⟩ := (pluck δ δ).1
    have e2 : algebraMap K 𝔸[K] ((δ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).submatrix (Fin.natAdd 2) c).det =
        (b : Matrix (Fin 2) (Fin 2) 𝔸[K]).det * ((((k : AdelicGLn.AdelicGL K (2 + 2)) * h⁻¹ : AdelicGLn.AdelicGL K (2 + 2)) :
          Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]).submatrix (Fin.natAdd 2) c).det := by
      rw [← Matrix.det_mul, ← hpq_rows X ((m₁ : AdelicGLn.AdelicGL K 2) * zt K t) b, ← Units.val_mul, ← e1, RingHom.map_det]
      rfl
    have h3 := hpq_minor ((k : AdelicGLn.AdelicGL K (2 + 2)) * h⁻¹) (Fin.natAdd 2) c
      ((AdelicGLn.det K 2 b)⁻¹ * GroundTheory.Global.IdeleGroup.diagonal K (Units.mk0 _ hc)) (by
        rw [Units.val_mul, GroundTheory.Global.IdeleGroup.coe_diagonal, Units.val_mk0, e2, ← AdelicGLn.coe_det, Units.inv_mul_cancel_left])
    rw [map_mul, GroundTheory.Global.IdeleGroup.ideleModule_diagonal, mul_one, map_inv, Positive.coe_inv] at h3
    change (detModule K 2 b : ℝ)⁻¹ ≤ _ at h3
    rw [hb', Real.exp_neg, inv_inv] at h3
    have h4 := height_mul_le (k : AdelicGLn.AdelicGL K (2 + 2)) h⁻¹
    rw [height_eq_one_of_mem_maxCompact (k := (k : AdelicGLn.AdelicGL K (2 + 2))) hk, mul_one, height_inv] at h4
    refine h3.trans ?_
    rw [hD, mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le h4 _) (Finset.prod_nonneg fun w _ => by positivity)
  have hs : 0 < Real.sqrt (Real.exp t / D) := Real.sqrt_pos.2 (div_pos (Real.exp_pos t) hD0)
  have hq : Real.sqrt (Real.exp t / D) ≤ qht g := by
    refine le_ciInf fun γ => ?_
    rw [Real.sqrt_le_left (height_pos _).le, div_le_iff₀ hD0, mul_comm]
    exact key γ
  have h5 := Real.log_le_log hs hq
  rw [Real.log_sqrt (div_pos (Real.exp_pos t) hD0).le, Real.log_div (Real.exp_pos t).ne' hD0.ne', Real.log_exp] at h5
  rw [ht]
  linarith
