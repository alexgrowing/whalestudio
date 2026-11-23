import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RangeDatumEmbedding
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroTop
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.DecDeriv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportInt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.CayleyIndep

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.DecLow

theorem frob_conj_eq {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayleyU k r ε P)
    (g : Mat k r) : frob (P * g * P⁻¹) = Formalism.FourierDecayAlt.B.gN g := by
  rw [szt_gN_eq, ← szt_hs_conj hP g]
  rfl

theorem decLow (k r : ℕ) (hk : 1 ≤ k) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H))
    (hlamR : Formalism.QuantumDeterminants.IsHCParam lam) (hDS : Formalism.MainNotions.S.IsDSHpk k r ε lam σ)
    (hgapAt : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hh : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h)
    (P : Mat k r) (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (w₁ w₂ : H)
    (h₁ : w₁ ∈ Formalism.MainNotions.S.lowKSub ε lam (fun g => σ (P⁻¹ * g * P)))
    (h₂ : w₂ ∈ Formalism.MainNotions.S.lowKSub ε lam (fun g => σ (P⁻¹ * g * P))) :
    ∃ C : ℝ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      ‖⟪w₂, σ x w₁⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN x ^ (-(h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))))) := by
  obtain ⟨P₀, hP₀, hds₀⟩ := hDS
  have hds := (cayleyIndep k r ε lam H σ P₀ P hP₀ hP hds₀).1
  obtain ⟨hp, hq⟩ := TransportInt.cayley_signature hP.1
  have hlam : S7.IsHCParam lam := (mir_isHCParam_iff lam).1 hlamR
  have hq0 : S7.q0 ε = r + 1 := by unfold S7.q0; rw [hp, hq]; omega
  have hq1 : 1 ≤ S7.q0 ε := by omega
  set N : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hpN : (pOf ε : ℝ) ≤ N := by rw [hN, hp]; exact_mod_cast (by omega : k + r ≤ 2 * r + k + 1)
  have hqN : (qOf ε : ℝ) ≤ N := by rw [hN, hq]; exact_mod_cast (by omega : r + 1 ≤ 2 * r + k + 1)
  have hq0N : (S7.q0 ε : ℝ) ≤ N := by rw [hN, hq0]; exact_mod_cast (by omega : r + 1 ≤ 2 * r + k + 1)
  have hN3 : (1 : ℝ) ≤ N ^ 3 := one_le_pow₀ hN1
  have hpq : N * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ N ^ 3 := by
    calc N * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ N * N * N := by gcongr
      _ = N ^ 3 := by ring
  have hnq : N * (S7.q0 ε : ℝ) ≤ N ^ 3 := by
    calc N * (S7.q0 ε : ℝ) ≤ N * N := by gcongr
      _ = N * N * 1 := by ring
      _ ≤ N * N * N := by gcongr
      _ = N ^ 3 := by ring
  have hgap : StdGap ε lam := ⟨hlam.1, h, hgapAt, by linarith⟩
  have h8 : 8 * N * (S7.q0 ε : ℝ) < h := by linarith
  have h0 : 0 < h := by linarith
  choose mm hmm using hlam.2
  let μ : Fin (2 * r + k + 1) → ℤ := fun a => mm a + ((2 * r + k + 1 : ℕ) : ℤ) - 1 - ((a : ℕ) : ℤ)
  have hμ : S7.IsMu lam μ := by
    unfold S7.IsMu
    intro a
    have ha := hmm a
    simp only [μ]
    unfold rho
    push_cast at ha ⊢
    linarith
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  have hΨ := (S7.isPsiFor_psiM ε lam h T μ hlam hμ hgapAt hq1 h8).1
  obtain ⟨j, -, -, hran, hF⟩ := anyF hds hgap hΨ
  obtain ⟨C, hC⟩ := S0.DecDeriv.psiM_frob_dec ε lam h T μ hlam hgapAt h0 hq1 hμ
  rw [← hran] at h₁ h₂
  obtain ⟨v₁, rfl⟩ := h₁
  obtain ⟨v₂, rfl⟩ := h₂
  refine ⟨‖v₂‖ * ‖v₁‖ * C, fun x hx => ?_⟩
  have hg := szt_conj_mem hP hx
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hback : P⁻¹ * (P * x * P⁻¹) * P = x := by
    have e : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
    calc P⁻¹ * (P * x * P⁻¹) * P = (P⁻¹ * P) * x * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [e, Matrix.one_mul, Matrix.mul_one]
  have hco : ⟪j v₂, σ x (j v₁)⟫_ℂ = ⟪v₂, S7.PsiM T μ (P * x * P⁻¹) v₁⟫_ℂ := by
    rw [← hF _ hg, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.comp_apply, hback]
  have hb := hC _ hg
  rw [frob_conj_eq hP, hq0] at hb
  push_cast at hb
  calc ‖⟪(j : T.V →ₗ[ℂ] H) v₂, σ x ((j : T.V →ₗ[ℂ] H) v₁)⟫_ℂ‖
      = ‖⟪v₂, S7.PsiM T μ (P * x * P⁻¹) v₁⟫_ℂ‖ := congrArg norm hco
    _ ≤ ‖v₂‖ * ‖S7.PsiM T μ (P * x * P⁻¹) v₁‖ := norm_inner_le_norm _ _
    _ ≤ ‖v₂‖ * (‖S7.PsiM T μ (P * x * P⁻¹)‖ * ‖v₁‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖v₂‖ * (C * Formalism.FourierDecayAlt.B.gN x ^ (-(h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))))) * ‖v₁‖) := by gcongr
    _ = _ := by ring

end ReciprocityTheory.ChartRestriction.DS.Lap.DecLow
