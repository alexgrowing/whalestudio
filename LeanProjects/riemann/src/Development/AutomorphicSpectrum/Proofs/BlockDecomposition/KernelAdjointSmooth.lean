import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

noncomputable section

open scoped ContDiff InnerProductSpace

namespace GlobalTheory.CompanionTheory.KerFc

def innerSmulRightR {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (e : V) :
    V →L[ℝ] (V →L[ℂ] V) :=
  LinearMap.mkContinuous
    { toFun := fun x => (innerSL ℂ x).smulRight e
      map_add' := fun x y => by
        ext w
        simp [inner_add_left, add_smul]
      map_smul' := fun r x => by
        ext w
        change ⟪r • x, w⟫_ℂ • e = r • (⟪x, w⟫_ℂ • e)
        rw [← Complex.coe_smul r x, inner_smul_left, Complex.conj_ofReal, mul_smul, Complex.coe_smul] }
    ‖e‖
    (fun x => by
      refine (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_)
      have h1 : ‖⟪x, w⟫_ℂ‖ ≤ ‖x‖ * ‖w‖ := norm_inner_le_norm x w
      simp only [LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, norm_smul]
      calc ‖⟪x, w⟫_ℂ‖ * ‖e‖ ≤ (‖x‖ * ‖w‖) * ‖e‖ := by gcongr
        _ = ‖e‖ * ‖x‖ * ‖w‖ := by ring)

theorem innerSmulRightR_apply {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (e x : V) :
    innerSmulRightR e x = (innerSL ℂ x).smulRight e := rfl

theorem adjoint_eq_sum {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] (B : V →L[ℂ] V) :
    ContinuousLinearMap.adjoint B =
      ∑ i, innerSmulRightR (stdOrthonormalBasis ℂ V i) (B (stdOrthonormalBasis ℂ V i)) := by
  ext w
  rw [ContinuousLinearMap.sum_apply]
  simp only [innerSmulRightR_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  rw [← (stdOrthonormalBasis ℂ V).sum_repr' (ContinuousLinearMap.adjoint B w)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]

theorem adjSmooth : AdjSmooth := by
  intro W V _ _ _ _ _ _ A s hA
  have hEq : (fun y => ContinuousLinearMap.adjoint (A y)) = fun y =>
      ∑ i, innerSmulRightR (stdOrthonormalBasis ℂ V i) (A y (stdOrthonormalBasis ℂ V i)) := by
    funext y
    exact adjoint_eq_sum (A y)
  rw [hEq]
  refine ContDiffOn.sum fun i _ => ?_
  exact (innerSmulRightR (stdOrthonormalBasis ℂ V i)).contDiff.comp_contDiffOn (hA _)

end GlobalTheory.CompanionTheory.KerFc
