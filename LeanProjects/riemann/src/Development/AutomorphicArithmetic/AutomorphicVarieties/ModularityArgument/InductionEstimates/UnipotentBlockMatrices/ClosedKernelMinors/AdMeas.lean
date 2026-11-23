import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

open scoped Matrix Kronecker in
private theorem adMeas_pi {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι 𝔸[K]) (u : (𝔸[K])ˣ) (hu : (u : 𝔸[K]) = M.det) :
    (Measure.pi fun _ : ι => GroundTheory.Global.adeleMeasure K).map (fun x => x ᵥ* M) =
      ENNReal.ofReal ((GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ))⁻¹ •
        Measure.pi fun _ : ι => GroundTheory.Global.adeleMeasure K := by
  let σ := Fintype.equivFin ι
  have hd : (Matrix.reindex σ σ M).det = u := by rw [Matrix.det_reindex_self, hu]
  let g : GL (Fin (Fintype.card ι)) 𝔸[K] :=
    Matrix.GeneralLinearGroup.mk'' (Matrix.reindex σ σ M) (hd ▸ u.isUnit)
  have hg : (g : Matrix _ _ 𝔸[K]) = Matrix.reindex σ σ M := rfl
  have hdet : Matrix.GeneralLinearGroup.det g = u := Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg, hd])
  have h := GJGlobal.Modulus.map_vecMul_adeleMeasurePi g
  rw [hdet] at h
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => 𝔸[K]) σ
  have hE : MeasurePreserving E (Measure.pi fun _ : ι => GroundTheory.Global.adeleMeasure K)
      (GJMatrix.adeleMeasurePi K) :=
    measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card ι) => GroundTheory.Global.adeleMeasure K) σ
  have hfun : (fun x : ι → 𝔸[K] => x ᵥ* M) =
      E.symm ∘ (fun x => x ᵥ* (g : Matrix _ _ 𝔸[K])) ∘ E := by
    funext x
    have hx : E x = x ∘ σ.symm := by
      funext i
      obtain ⟨j, rfl⟩ := σ.surjective i
      simp [E, MeasurableEquiv.piCongrLeft_apply_apply]
    funext i
    change _ = (E x ᵥ* (g : Matrix _ _ 𝔸[K])) (σ i)
    rw [hx, hg, Matrix.reindex_apply, Matrix.submatrix_vecMul_equiv]
    simp [Function.comp_assoc]
  have hm := GJGlobal.Modulus.measurable_vecMul' g
  rw [hfun, ← Measure.map_map E.symm.measurable (hm.comp E.measurable),
    ← Measure.map_map hm E.measurable, hE.map_eq, h, Measure.map_smul, hE.symm.map_eq]

private def adMeas_tau : Fin 2 × Fin 2 ≃ UPos (2 + 2) 2 where
  toFun p := ⟨(Fin.castAdd 2 p.1, Fin.natAdd 2 p.2), p.1.2, Nat.le_add_right _ _⟩
  invFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2 - 2, by have := p.1.2.2; omega⟩)
  left_inv := by decide
  right_inv := by decide

private theorem adMeas_unip {R : Type} [CommRing R] (X : UPos (2 + 2) 2 → R) :
    unipMatrix X = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks 1 (Matrix.of fun i j => X (adMeas_tau (i, j))) 0 1) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [unipMatrix, Matrix.add_apply, blockEntry_apply, Matrix.one_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] <;>
    fin_cases i <;> fin_cases j <;> simp [adMeas_tau, Fin.ext_iff]

open scoped Matrix Kronecker in
private noncomputable def adMeas_M {R : Type} [CommRing R] (a b : GL (Fin 2) R) :
    Matrix (UPos (2 + 2) 2) (UPos (2 + 2) 2) R :=
  Matrix.reindex adMeas_tau adMeas_tau (((a⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)ᵀ ⊗ₖ (b : Matrix (Fin 2) (Fin 2) R))

private theorem adMeas_M_mul {R : Type} [CommRing R] (a b : GL (Fin 2) R) :
    adMeas_M a b * adMeas_M a⁻¹ b⁻¹ = 1 := by
  simp only [adMeas_M, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul, ← Units.val_mul, ← Units.val_mul]
  simp

open scoped Matrix in
private theorem adMeas_conj {R : Type} [CommRing R] (a b : GL (Fin 2) R) (X : UPos (2 + 2) 2 → R) :
    unipGL X * blk a b = blk a b * unipGL (X ᵥ* adMeas_M a b) := by
  have h : (Matrix.of fun i j => (X ᵥ* adMeas_M a b) (adMeas_tau (i, j))) =
      ((a⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * (Matrix.of fun i j => X (adMeas_tau (i, j))) *
        (b : Matrix (Fin 2) (Fin 2) R) := by
    ext i j
    rw [adMeas_M, Matrix.reindex_apply, Matrix.of_apply, Matrix.submatrix_vecMul_equiv]
    simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm, Matrix.vecMul, dotProduct,
      Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.of_apply, Fin.sum_univ_two]
    ring
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_unipGL, coe_unipGL, adMeas_unip, adMeas_unip, h]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel]
  simp

open scoped Matrix in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.adMeas :
    ∀ {K : Type} [Field K] [NumberField K] (m₁ m₂ : G1 K 2) (t : ℝ), ∃ e : (UPos (2 + 2) 2 → 𝔸[K]) ≃ₜ+ (UPos (2 + 2) 2 → 𝔸[K]), (∀ X, nn X * lv m₁ m₂ t = lv m₁ m₂ t * nn (e X)) ∧
      (unipMeasure K (2 + 2) 2).map e = ENNReal.ofReal (Real.exp (4 * t)) • unipMeasure K (2 + 2) 2 := by
  intro K _ _ m₁ m₂ t
  set a : AdelicGLn.AdelicGL K 2 := (m₁ : AdelicGLn.AdelicGL K 2) * zt K t with ha
  set b : AdelicGLn.AdelicGL K 2 := (m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t) with hb
  have h2 : adMeas_M a⁻¹ b⁻¹ * adMeas_M a b = 1 := by
    simpa using adMeas_M_mul a⁻¹ b⁻¹
  refine ⟨{ toFun := fun X => X ᵥ* adMeas_M a b
            invFun := fun X => X ᵥ* adMeas_M a⁻¹ b⁻¹
            left_inv := fun X => by simp only [Matrix.vecMul_vecMul, adMeas_M_mul, Matrix.vecMul_one]
            right_inv := fun X => by simp only [Matrix.vecMul_vecMul, h2, Matrix.vecMul_one]
            map_add' := fun X Y => Matrix.add_vecMul _ _ _
            continuous_toFun := continuous_id.matrix_vecMul continuous_const
            continuous_invFun := continuous_id.matrix_vecMul continuous_const }, fun X => ?_, ?_⟩
  · refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, (blkLaws (K := K)).1 m₁ m₂ t]
    exact adMeas_conj a b X
  · have hm : ∀ (m : G1 K 2) (s : ℝ),
        (detModule K 2 ((m : AdelicGLn.AdelicGL K 2) * zt K s) : ℝ) = Real.exp s := by
      intro m s
      rw [map_mul, mem_normOneGL_iff_detModule.1 m.2, one_mul, zt, detModule_centralSection two_pos]
    have h := adMeas_pi (adMeas_M a b)
      (Matrix.GeneralLinearGroup.det a⁻¹ ^ 2 * Matrix.GeneralLinearGroup.det b ^ 2) (by
        rw [adMeas_M, Matrix.det_reindex_self, Matrix.det_kronecker, Matrix.det_transpose]
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply,
          Fintype.card_fin])
    have hv : ((GroundTheory.Global.IdeleGroup.ideleModule K
        (Matrix.GeneralLinearGroup.det a⁻¹ ^ 2 * Matrix.GeneralLinearGroup.det b ^ 2) : ℝ))⁻¹ =
        Real.exp (4 * t) := by
      have e1 : GroundTheory.Global.IdeleGroup.ideleModule K
          (Matrix.GeneralLinearGroup.det a⁻¹ ^ 2 * Matrix.GeneralLinearGroup.det b ^ 2) =
          (detModule K 2 a)⁻¹ ^ 2 * detModule K 2 b ^ 2 := by
        rw [map_mul, map_pow, map_pow, ← map_inv (detModule K 2)]
        rfl
      rw [e1, Positive.val_mul, Positive.val_pow, Positive.val_pow, Positive.coe_inv, hm, hm,
        ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_neg]
      congr 1
      push_cast
      ring
    rw [hv] at h
    exact h
