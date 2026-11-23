import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.SumNormAdjointSqEqHsOp

noncomputable section

open Finset Matrix

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem polar_pP {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ∃ k : KG ε, g = toMK k * pP g := by
  obtain ⟨u, hu⟩ := exists_toMK (PolarDecomposition.polar_k_mem hg)
  refine ⟨u, ?_⟩
  rw [hu, pP, Matrix.mul_assoc, PolarDecomposition.polar_exp_neg_mul, Matrix.mul_one]

theorem hsOp_op_mul {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) (A : T.V →L[ℂ] T.V) :
    hsOp (T.op k * A) = hsOp A := by
  unfold hsOp
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.mul_apply, KType_norm_op_apply]

theorem hsPol : HsPol := by
  intro n ε g hg
  refine ⟨⟨PolarDecomposition.polar_L g, PolarDecomposition.polar_L_inP hg, rfl⟩, fun Λ T μ => ?_⟩
  obtain ⟨k, hk⟩ := polar_pP hg
  have hL := PolarDecomposition.polar_L_inP hg
  have hex : ∃ (k' : KG ε) (X' : Matrix (Fin n) (Fin n) ℂ), inP ε X' ∧ g = toMK k' * NormedSpace.exp X' :=
    ⟨k, PolarDecomposition.polar_L g, hL, hk⟩
  unfold PsiM
  rw [dif_pos hex]
  obtain ⟨hP, hEq⟩ := hex.choose_spec.choose_spec
  have hEq' : toMK k * NormedSpace.exp (PolarDecomposition.polar_L g) = toMK hex.choose * NormedSpace.exp hex.choose_spec.choose :=
    hk.symm.trans hEq
  obtain ⟨-, h2⟩ := polar_unique hL hP hEq'
  rw [hsOp_op_mul, ← h2]
  rfl

end CompanionTheory.RgFd
