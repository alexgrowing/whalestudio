import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrableOfDecayVG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InhabRep

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra

lemma coefOp_apply_le_frob (A : Matrix (Fin n) (Fin n) ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A v‖ ≤ ‖A‖ * ‖v‖ := by
  have h1 : Matrix.toEuclideanCLM (𝕜 := ℂ) A v = WithLp.toLp 2 (A *ᵥ WithLp.ofLp v) := rfl
  rw [h1, ← Matrix.frobenius_norm_replicateCol (ι := Fin 1), Matrix.replicateCol_mulVec]
  calc ‖A * Matrix.replicateCol (Fin 1) (WithLp.ofLp v)‖
      ≤ ‖A‖ * ‖Matrix.replicateCol (Fin 1) (WithLp.ofLp v)‖ := Matrix.frobenius_norm_mul _ _
    _ = ‖A‖ * ‖v‖ := by
      congr 1
      exact Matrix.frobenius_norm_replicateCol (ι := Fin 1) (WithLp.ofLp v)

end Frob

lemma coefOp_norm_exp_clm (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    ‖NormedSpace.exp T‖ ≤ Real.exp ‖T‖ := by
  rw [NormedSpace.exp_eq_tsum ℂ, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
  dsimp only
  refine (norm_tsum_le_tsum_norm (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) T)).trans ?_
  refine Summable.tsum_le_tsum (fun k => ?_) (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) T)
    (NormedSpace.expSeries_summable' (𝕂 := ℝ) ‖T‖)
  rw [norm_smul, smul_eq_mul, norm_inv, Complex.norm_natCast]
  gcongr
  cases k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ k => exact norm_pow_le' T (Nat.succ_pos k)

lemma coefOp_unitary_le_one {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) k‖ ≤ 1 := by
  have hU : star (Matrix.toEuclideanCLM (𝕜 := ℂ) k) * Matrix.toEuclideanCLM (𝕜 := ℂ) k = 1 := by
    rw [← map_star, ← map_mul, Unitary.star_mul_self_of_mem hk, map_one]
  have h := CStarRing.norm_star_mul_self (x := Matrix.toEuclideanCLM (𝕜 := ℂ) k)
  rw [hU] at h
  have h1 : ‖(1 : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) k)]

theorem coefOp_le_sqrt_hs (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ Real.sqrt (S7.hs A) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
  have h := coefOp_apply_le_frob A v
  rwa [← S7.sqrt_hs_frobVG A] at h

theorem coefOp_unitary_mul_exp {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (k * NormedSpace.exp X)‖ ≤ Real.exp (Real.sqrt (S7.hs X)) := by
  have hc : Continuous (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hexp : Matrix.toEuclideanCLM (𝕜 := ℂ) (NormedSpace.exp X) =
      NormedSpace.exp (Matrix.toEuclideanCLM (𝕜 := ℂ) X) := by
    let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedRing
    let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAlgebra
    refine NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) _ hc X ?_
    rw [NormedSpace.expSeries_radius_eq_top]
    simp
  rw [map_mul, hexp]
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℂ) k * NormedSpace.exp (Matrix.toEuclideanCLM (𝕜 := ℂ) X)‖
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) k‖ * ‖NormedSpace.exp (Matrix.toEuclideanCLM (𝕜 := ℂ) X)‖ :=
        norm_mul_le _ _
    _ ≤ 1 * Real.exp (Real.sqrt (S7.hs X)) :=
        mul_le_mul (coefOp_unitary_le_one hk)
          ((coefOp_norm_exp_clm _).trans (Real.exp_le_exp.mpr (coefOp_le_sqrt_hs X)))
          (norm_nonneg _) zero_le_one
    _ = Real.exp (Real.sqrt (S7.hs X)) := one_mul _

theorem coefOp_kexp {ε : Fin n → Bool} (k : S7.KG ε) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toMK k * NormedSpace.exp X)‖ ≤ Real.exp (Real.sqrt (S7.hs X)) := by
  have hk : S7.toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    exact (S7.toMK_facts k).2.1
  exact coefOp_unitary_mul_exp hk X

end ReciprocityTheory.ChartRestriction.DS
