import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RangeDatumEmbedding
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiGelfand
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem coef_continuousOn_le_one (hDS : Formalism.MainNotions.S.IsDS ε lam σ) {w : H}
    (hw : Formalism.MainNotions.S.IsLowUnit ε lam σ w) :
    ContinuousOn (fun g => ⟪w, σ g w⟫_ℂ) {g | inUJ ε g} ∧ ∀ g, inUJ ε g → ‖⟪w, σ g w⟫_ℂ‖ ≤ 1 := by
  obtain ⟨-, -, ⟨-, hnorm, hcont⟩, -⟩ := hDS
  obtain ⟨hw1, -⟩ := hw
  refine ⟨?_, fun g hg => ?_⟩
  · exact continuousOn_const.inner (hcont w)
  · calc ‖⟪w, σ g w⟫_ℂ‖ ≤ ‖w‖ * ‖σ g w‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [hnorm g hg w, hw1, one_mul]

theorem coef_dec_of_isDS [CompleteSpace H] (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hlam : Formalism.QuantumDeterminants.IsHCParam lam)
    {h : ℝ} (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hq : 1 ≤ S7.q0 ε) (h8 : 8 * (n : ℝ) * S7.q0 ε < h)
    (hstd : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {w : H} (hw : Formalism.MainNotions.S.IsLowUnit ε lam σ w)
    (k : S7.KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    ‖⟪w, σ (S7.toMK k * NormedSpace.exp X) w⟫_ℂ‖ ≤
      Real.exp (-(h / 8) * min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * S7.q0 ε))) := by
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨Ψ, hP, hdec⟩ := exists_isPsiFor S7.psiExists T hlam hgap hq h8
  have hsg : StdGap ε lam := ⟨hlam.1, h, hgap, hstd⟩
  obtain ⟨j, hj, -, hrange, hadj⟩ := anyF hDS hsg hP
  obtain ⟨hw1, hwS⟩ := hw
  rw [← hrange] at hwS
  obtain ⟨v, rfl⟩ := hwS
  have hexp : NormedSpace.exp X ∈ UJset ε := by
    have := rq_exp_mem ε X hX.1 1
    rwa [Complex.ofReal_one, one_smul] at this
  have hg : S7.toMK k * NormedSpace.exp X ∈ UJset ε := rq_UJ_mul (ffa_toMK_mem k) hexp
  have hv1 : ‖v‖ = 1 := by rw [← hj v]; exact hw1
  have e : ⟪j v, σ (S7.toMK k * NormedSpace.exp X) (j v)⟫_ℂ =
      ⟪v, Ψ (S7.toMK k * NormedSpace.exp X) v⟫_ℂ := by
    rw [← hadj _ hg, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right]
  change ‖⟪j v, σ (S7.toMK k * NormedSpace.exp X) (j v)⟫_ℂ‖ ≤ _
  rw [e]
  calc ‖⟪v, Ψ (S7.toMK k * NormedSpace.exp X) v⟫_ℂ‖
      ≤ ‖v‖ * ‖Ψ (S7.toMK k * NormedSpace.exp X) v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖Ψ (S7.toMK k * NormedSpace.exp X)‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖Ψ (S7.toMK k * NormedSpace.exp X)‖ := by rw [hv1]; ring
    _ ≤ _ := hdec k X hX

end ReciprocityTheory.ChartRestriction.DS
