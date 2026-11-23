import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarMirror
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem pl_opNorm_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (A : V →L[ℂ] V) : ‖A‖ ^ 2 ≤ (Module.finrank ℂ V : ℝ) * hsOp A := by
  set b := stdOrthonormalBasis ℂ V
  have h1 : ‖A‖ ≤ ∑ i, ‖A (b i)‖ := by
    refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
    conv_lhs => rw [← b.sum_repr' v]
    rw [map_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_smul, norm_smul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖⟪b i, v⟫_ℂ‖ ≤ ‖b i‖ * ‖v‖ := norm_inner_le_norm _ _
      _ = ‖v‖ := by rw [b.orthonormal.1 i, one_mul]
  have h2 : (∑ i, ‖A (b i)‖) ^ 2 ≤ (Finset.univ.card : ℝ) * ∑ i, ‖A (b i)‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  have hc : (Finset.univ : Finset (Fin (Module.finrank ℂ V))).card = Module.finrank ℂ V := by simp
  calc ‖A‖ ^ 2 ≤ (∑ i, ‖A (b i)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by rw [hc] at h2; exact h2

theorem square_integrable_of_norm : PsiNorm → CompanionTheory.RgDs.ExplicitFunctionSquareIntegrable := by
  intro hN n ε lam T μ hl hμ ν hν
  have hfin := hN n ε lam hl T μ hμ
  have := muCD_isHaar ε
  set f : UJ ε → (T.V →L[ℂ] T.V) := fun g => PsiM T μ (toM g) with hf
  have hcont : Continuous f :=
    (psiM_continuousOn T μ hμ).comp_continuous (continuous_toM ε) (fun g => g.2)
  have hmCD : MemLp f 2 (muCD ε) := by
    refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ⟨(hcont.norm.pow 2).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have hle : ∀ g : Formalism.REAL.UJ ε, ‖‖f g‖ ^ 2‖ₑ ≤
        ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) * ENNReal.ofReal (hsOp (PsiM T μ (Formalism.MainNotions.S.umat g))) := by
      intro g
      rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _), Real.enorm_eq_ofReal (by positivity)]
      exact ENNReal.ofReal_le_ofReal (pl_opNorm_le _)
    calc ∫⁻ g, ‖‖f g‖ ^ 2‖ₑ ∂(muCD ε) ≤ ∫⁻ g : Formalism.REAL.UJ ε, ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) *
          ENNReal.ofReal (hsOp (PsiM T μ (Formalism.MainNotions.S.umat g))) ∂(muCD ε) := lintegral_mono hle
      _ = ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) *
          ∫⁻ g : Formalism.REAL.UJ ε, ENNReal.ofReal (hsOp (PsiM T μ (Formalism.MainNotions.S.umat g))) ∂(muCD ε) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := by rw [hfin]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  haveI hH : (show Measure (UJ ε) from muCD ε).IsHaarMeasure := muCD_isHaar ε
  have heq := Measure.isMulLeftInvariant_eq_smul ν (show Measure (UJ ε) from muCD ε)
  rw [heq]
  exact hmCD.smul_measure ENNReal.coe_ne_top

end CompanionTheory.RgFd
