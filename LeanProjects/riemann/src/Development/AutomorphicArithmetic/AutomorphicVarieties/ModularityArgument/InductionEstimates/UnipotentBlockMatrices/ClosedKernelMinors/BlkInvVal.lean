import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] {a b : ℕ}

private theorem blk_val (x : GL (Fin a) R) (y : GL (Fin b) R) :
    (blk x y).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x.val 0 0 y.val) := rfl

private theorem blk_inv_val (x : GL (Fin a) R) (y : GL (Fin b) R) :
    (blk x y)⁻¹ = blk x⁻¹ y⁻¹ := Units.ext rfl

private theorem wGL_val :
    (wGL R).val = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks 0 (1 : Matrix (Fin 2) (Fin 2) R) 1 0) := rfl

private theorem wGL_inv : (wGL R)⁻¹ = wGL R := Units.ext rfl

private theorem blk_mul' (x x' : GL (Fin a) R) (y y' : GL (Fin b) R) :
    blk x y * blk x' y' = blk (x * x') (y * y') := by
  apply Units.ext
  simp only [Units.val_mul, blk_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

private theorem blk_one' : blk (1 : GL (Fin a) R) (1 : GL (Fin b) R) = 1 := by
  apply Units.ext
  simp only [blk_val, Units.val_one, Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

private theorem w_blk (x y : GL (Fin 2) R) : wGL R * blk x y = blk y x * wGL R := by
  apply Units.ext
  simp only [Units.val_mul, blk_val, wGL_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]

private theorem blk_det (x : GL (Fin a) R) (y : GL (Fin b) R) :
    Matrix.GeneralLinearGroup.det (blk x y) = Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det y := by
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, blk_val, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₂₁]

private theorem blk_map (f : R →+* S) (x : GL (Fin a) R) (y : GL (Fin b) R) :
    (blk x y).val.map f =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (x.val.map f) 0 0 (y.val.map f)) := by
  ext i j
  simp only [blk_val, Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

private theorem w_map (f : R →+* S) : (wGL R).val.map f = (wGL S).val := by
  ext i j
  simp only [wGL_val, Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;>
    simp [Matrix.one_apply, apply_ite f]

private theorem blk_cont [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun p : GL (Fin a) R × GL (Fin b) R => blk p.1 p.2 := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Continuous.matrix_fromBlocks (Units.continuous_val.comp continuous_fst) continuous_const continuous_const
      (Units.continuous_val.comp continuous_snd)).matrix_reindex _ _
  · exact (Continuous.matrix_fromBlocks (Units.continuous_coe_inv.comp continuous_fst) continuous_const continuous_const
      (Units.continuous_coe_inv.comp continuous_snd)).matrix_reindex _ _

private theorem blk_ent (O : Subring S) (x : GL (Fin a) S) (y : GL (Fin b) S) (hx : ∀ i j, x i j ∈ O)
    (hy : ∀ i j, y i j ∈ O) (i j : Fin (a + b)) : blk x y i j ∈ O := by
  change (blk x y).val i j ∈ O
  simp only [blk_val, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [hx, hy]

private theorem w_ent (O : Subring S) (i j : Fin (2 + 2)) : wGL S i j ∈ O := by
  change (wGL S).val i j ∈ O
  simp only [wGL_val, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply, O.zero_mem] <;>
    split_ifs <;> simp

private theorem vec_l (M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) S) (y : Fin (a + b) → S) (j : Fin a ⊕ Fin b) :
    Matrix.vecMul y (Matrix.reindex finSumFinEquiv finSumFinEquiv M) (finSumFinEquiv j) =
      ∑ i : Fin a, y (finSumFinEquiv (Sum.inl i)) * M (Sum.inl i) j +
        ∑ i : Fin b, y (finSumFinEquiv (Sum.inr i)) * M (Sum.inr i) j := by
  simp only [Matrix.vecMul, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [Equiv.symm_apply_apply]

end SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
private theorem blk_arch {a b : ℕ} (w : InfinitePlace K) {x : GL (Fin a) w.Completion} {y : GL (Fin b) w.Completion}
    (hx : x ∈ archCompact w) (hy : y ∈ archCompact w) : blk x y ∈ archCompact (n := a + b) w := by
  intro z
  refine (sq_eq_sq₀ (euclidNorm_nonneg _) (euclidNorm_nonneg _)).1 ?_
  have h1 := congrArg (· ^ 2) (hx fun i => z (finSumFinEquiv (Sum.inl i)))
  have h2 := congrArg (· ^ 2) (hy fun i => z (finSumFinEquiv (Sum.inr i)))
  simp only [euclidNorm_sq, Matrix.vecMul, dotProduct] at h1 h2
  rw [euclidNorm_sq, euclidNorm_sq, ← finSumFinEquiv.sum_comp, ← finSumFinEquiv.sum_comp (fun i => ‖z i‖ ^ 2),
    Fintype.sum_sum_type, Fintype.sum_sum_type, ← h1, ← h2]
  simp only [blk_val, vec_l, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add]

omit [NumberField K] in
private theorem w_arch (w : InfinitePlace K) : wGL w.Completion ∈ archCompact (n := 2 + 2) w := by
  intro z
  refine (sq_eq_sq₀ (euclidNorm_nonneg _) (euclidNorm_nonneg _)).1 ?_
  rw [euclidNorm_sq, euclidNorm_sq, ← finSumFinEquiv.sum_comp, ← finSumFinEquiv.sum_comp (fun i => ‖z i‖ ^ 2),
    Fintype.sum_sum_type, Fintype.sum_sum_type, add_comm]
  simp only [wGL_val, vec_l, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add,
      Matrix.one_apply, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem blk_max {a b : ℕ} {x : AdelicGLn.AdelicGL K a} {y : AdelicGLn.AdelicGL K b}
    (hx : x ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K a)))
    (hy : y ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K b))) :
    blk x y ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (a + b))) := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have : infAt w (blk x y) = blk (infAt w x) (infAt w y) :=
      Units.ext (Matrix.ext fun i j => congrArg (fun N => N i j) (blk_map (infEval w) x y))
    rw [this]
    exact blk_arch w (hx.1 w) (hy.1 w)
  · have : finAt v (blk x y) = blk (finAt v x) (finAt v y) :=
      Units.ext (Matrix.ext fun i j => congrArg (fun N => N i j) (blk_map (finEval v) x y))
    rw [this, GLnLocal.mem_integralGL_iff, blk_inv_val]
    have h1 := (GLnLocal.mem_integralGL_iff _ _).1 (hx.2 v)
    have h2 := (GLnLocal.mem_integralGL_iff _ _).1 (hy.2 v)
    exact ⟨blk_ent _ _ _ h1.1 h2.1, blk_ent _ _ _ h1.2 h2.2⟩

private theorem w_max : wGL 𝔸[K] ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))) := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have : infAt w (wGL 𝔸[K]) = wGL _ :=
      Units.ext (Matrix.ext fun i j => congrArg (fun N => N i j) (w_map (infEval w)))
    rw [this]
    exact w_arch w
  · have : finAt v (wGL 𝔸[K]) = wGL _ :=
      Units.ext (Matrix.ext fun i j => congrArg (fun N => N i j) (w_map (finEval v)))
    rw [this, GLnLocal.mem_integralGL_iff, wGL_inv]
    exact ⟨w_ent _, w_ent _⟩

private theorem det_blk (a b : AdelicGLn.AdelicGL K 2) :
    detModule K (2 + 2) (blk a b) = detModule K 2 a * detModule K 2 b := by
  simp only [detModule, MonoidHom.comp_apply, AdelicGLn.det, blk_det, map_mul]

private theorem coe_ret {n : ℕ} {g : AdelicGLn.AdelicGL K n} (h : g ∈ normOneGL K n) :
    (retractOne g : AdelicGLn.AdelicGL K n) = g :=
  congrArg Subtype.val (retractOne_coe (⟨g, h⟩ : normOneGL K n))

private theorem zt_add (s t : ℝ) : zt K (s + t) = zt K s * zt K t := by
  rw [zt, zt, zt, ← map_mul]
  exact congrArg _ (Subtype.ext (Real.exp_add s t))

private theorem zt_zero : zt K 0 = 1 := by
  rw [zt, ← map_one (centralSection K 2)]
  exact congrArg _ (Subtype.ext Real.exp_zero)

private theorem lv_coe (m₁ m₂ : G1 K 2) (t : ℝ) :
    ((lv m₁ m₂ t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk ((m₁ : AdelicGLn.AdelicGL K 2) * zt K t) ((m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t)) := by
  refine coe_ret (mem_normOneGL_iff_detModule.2 ?_)
  rw [det_blk, map_mul, map_mul, mem_normOneGL_iff_detModule.1 m₁.2, mem_normOneGL_iff_detModule.1 m₂.2,
    one_mul, one_mul, ← map_mul, ← zt_add, add_neg_cancel, zt_zero, map_one]

private theorem mul_zt (m m' : AdelicGLn.AdelicGL K 2) (s t : ℝ) :
    m * zt K s * (m' * zt K t) = m * m' * zt K (s + t) := by
  rw [zt_add, mul_assoc, ← mul_assoc (zt K s), show zt K s * m' = m' * zt K s from centralSection_mul_comm _ _]
  simp only [mul_assoc]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.blkLaws :
    ∀ {K : Type} [Field K] [NumberField K], (∀ (m₁ m₂ : G1 K 2) (t : ℝ), ((lv m₁ m₂ t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = blk ((m₁ : AdelicGLn.AdelicGL K 2) * zt K t) ((m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t))) ∧
      (∀ (m₁ m₂ m₁' m₂' : G1 K 2) (t t' : ℝ), lv m₁ m₂ t * lv m₁' m₂' t' = lv (m₁ * m₁') (m₂ * m₂') (t + t')) ∧ lv (1 : G1 K 2) 1 0 = 1 ∧
      Continuous (fun p : G1 K 2 × G1 K 2 × ℝ => lv p.1 p.2.1 p.2.2) ∧
      (∀ a b : AdelicGLn.AdelicGL K 2, detModule K (2 + 2) (blk a b) = detModule K 2 a * detModule K 2 b) ∧
      (∀ a b a' b' : AdelicGLn.AdelicGL K 2, blk a b * blk a' b' = blk (a * a') (b * b')) ∧
      ((w0 K : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = wGL 𝔸[K] ∧ w0 K ∈ Gam K (2 + 2) ∧ w0 K ∈ KG K (2 + 2) ∧
      (∀ (m₁ m₂ : G1 K 2) (t : ℝ), w0 K * lv m₁ m₂ t = lv m₂ m₁ (-t) * w0 K) ∧
      (∀ u₁ ∈ KG K 2, ∀ u₂ ∈ KG K 2, lv u₁ u₂ 0 ∈ KG K (2 + 2)) ∧ ∀ n, IsCompact (KG K n : Set (G1 K n)) ∧
        ∀ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)), k ∈ normOneGL K n := by
  intro K _ _
  have hw : ((w0 K : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = wGL 𝔸[K] :=
    coe_ret (maxCompact_le_normOneGL w_max)
  have hz : Continuous (zt K) := continuous_centralSection.comp (Real.continuous_exp.subtype_mk _)
  refine ⟨lv_coe, ?_, ?_, ?_, det_blk, fun a b a' b' => blk_mul' a a' b b', hw, ?_, ?_, ?_, ?_, fun n => ⟨?_, ?_⟩⟩
  · intro m₁ m₂ m₁' m₂' t t'
    apply Subtype.ext
    rw [Subgroup.coe_mul, lv_coe, lv_coe, lv_coe, blk_mul', mul_zt, mul_zt, neg_add, Subgroup.coe_mul, Subgroup.coe_mul]
  · apply Subtype.ext
    rw [lv_coe, neg_zero, zt_zero, Subgroup.coe_one, Subgroup.coe_one, mul_one, blk_one']
  · exact continuous_retractOne.comp (blk_cont.comp
      (((continuous_subtype_val.comp continuous_fst).mul (hz.comp continuous_snd.snd)).prodMk
        ((continuous_subtype_val.comp continuous_snd.fst).mul (hz.comp continuous_snd.snd.neg))))
  · change ((w0 K : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈ AdelicGLn.rationalGL K (2 + 2)
    rw [hw]
    exact ⟨wGL K, Units.ext (w_map (algebraMap K 𝔸[K]))⟩
  · change ((w0 K : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈ Reduction.maxCompact
    rw [hw]
    exact w_max
  · intro m₁ m₂ t
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, lv_coe, lv_coe, hw, neg_neg, w_blk]
  · intro u₁ h₁ u₂ h₂
    change ((lv u₁ u₂ 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈ Reduction.maxCompact
    rw [lv_coe, neg_zero, zt_zero, mul_one, mul_one]
    exact blk_max h₁ h₂
  · refine Topology.IsInducing.subtypeVal.isCompact_preimage' isCompact_maxCompact ?_
    intro k hk
    exact ⟨⟨k, maxCompact_le_normOneGL hk⟩, rfl⟩
  · exact fun k hk => maxCompact_le_normOneGL hk
