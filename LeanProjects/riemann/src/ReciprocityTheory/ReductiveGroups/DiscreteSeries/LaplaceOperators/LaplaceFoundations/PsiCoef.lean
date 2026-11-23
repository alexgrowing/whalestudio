import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.NormPsiGen

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS Formalism.QuantumDeterminants SchurOrthogonalityLemmas

theorem b7b : WhittakerSchurOrthogonality := by
  intro k r ε Λ T μ P u c Vp _ _ _ π ξ μW μN _ hP hW hπ hξn hξ hΛ hμW hμ1 _ hcont hint
  classical
  set ψ := Formalism.MainNotions.S.psiGen k r (z0 k r) c with hψ
  set π' : Matrix (Fin k) (Fin k) ℂ → (Vp →L[ℂ] Vp) := fun h => π (Formalism.MainNotions.S.blockW k r h) with hπ'
  have hUR := hπ.2.2.1
  have : FiniteDimensional ℂ Vp := hπ.2.1
  have : IsProbabilityMeasure μW := ⟨hμ1⟩
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r (z0 k r) := by
    rw [ae_iff]; simpa using hμW.2.2.1
  have haeP : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r (z0 k r) :=
    Measure.quasiMeasurePreserving_fst.ae hae
  set F : Mt k r × Mt k r → Vp := fun p =>
    psiCoef T μ P T.w T.w ((1 : Mat k r)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * 1)) •
      chiInv ψ π (Matrix.of p.1) (Matrix.of p.2) ξ with hF
  have hA : aaFun T μ P μW μN ψ π T.w T.w ξ 1 1 = ∫ p, F p ∂(μW.prod μN) := rfl
  have hK : ∀ h : Mt k r, Matrix.of h ∈ UWset k r (z0 k r) → P * Matrix.of h * P⁻¹ ∈ Kset ε := by
    intro h hh
    rw [StandardBasisEmbedding.eq_blockW hh, cay_kE hP hW]
    exact kE_mem_Kset (fun a ha => cay_eps hP hW a ha) (StandardBasisEmbedding.blk_unitary hh)
  have hPsi : ∀ h m : Mt k r, Matrix.of h ∈ UWset k r (z0 k r) →
      S7.PsiM T μ (P * (Matrix.of h * Matrix.of m) * P⁻¹) =
        HW.torepSig T (P * Matrix.of h * P⁻¹) * S7.PsiM T μ (P * Matrix.of m * P⁻¹) := by
    intro h m hh
    have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
    have e : P * (Matrix.of h * Matrix.of m) * P⁻¹ = (P * Matrix.of h * P⁻¹) * (P * Matrix.of m * P⁻¹) := by
      have : (P * Matrix.of h * P⁻¹) * (P * Matrix.of m * P⁻¹) =
          P * Matrix.of h * (P⁻¹ * P) * Matrix.of m * P⁻¹ := by simp only [Matrix.mul_assoc]
      rw [this, Matrix.nonsing_inv_mul _ hu]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [e, psiM_K T μ (hK h hh)]
  have hunit : ∀ g ∈ UWset k r (z0 k r), ∀ v, ‖π g v‖ = ‖v‖ := by
    intro g hg v
    rw [StandardBasisEmbedding.eq_blockW hg]
    exact hUR.2.1 _ (unit_uj (StandardBasisEmbedding.blk_unitary hg)) v
  have hinvG : ∀ h : Mt k r, Matrix.of h ∈ UWset k r (z0 k r) → (Matrix.of h)⁻¹ ∈ UWset k r (z0 k r) := by
    intro h hh
    rw [(uw_inv hh).1]
    exact StandardBasisEmbedding.mem_UW (Unitary.star_mem (StandardBasisEmbedding.blk_unitary hh))
  have hFm : AEStronglyMeasurable F (μW.prod μN) := by
    have hc0 : Continuous (fun p : Mt k r × Mt k r =>
        (P * ((1 : Mat k r)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * 1)) * P⁻¹ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := by
      fun_prop
    have hc1 : Continuous (fun p : Mt k r × Mt k r =>
        (Matrix.of.symm (P * ((1 : Mat k r)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * 1)) * P⁻¹) : Mt k r)) := by
      exact hc0
    have h1 : Measurable (fun p : Mt k r × Mt k r =>
        psiCoef T μ P T.w T.w ((1 : Mat k r)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * 1))) := by
      exact (coef_meas T μ hcont T.w T.w).comp hc1.measurable
    have h2 : Continuous (fun p : Mt k r × Mt k r => star (ψ (Matrix.of p.2))) :=
      continuous_star.comp ((psiGen_cont _ _).comp continuous_snd)
    have h3 : AEStronglyMeasurable (fun p : Mt k r × Mt k r => π (Matrix.of p.1)⁻¹ ξ) (μW.prod μN) := by
      have hc : ContinuousOn (fun x : Mt k r => π' (star (StandardBasisEmbedding.blk (Matrix.of x))) ξ)
          {x | Matrix.of x ∈ UWset k r (z0 k r)} :=
        (hUR.2.2 ξ).comp blk_cont.star.continuousOn
          (fun x hx => unit_uj (Unitary.star_mem (StandardBasisEmbedding.blk_unitary hx)))
      have h0 := hc.aestronglyMeasurable (μ := μW) isClosed_UW.measurableSet
      rw [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ UWset k r (z0 k r)}) hae] at h0
      have h0' : AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x)⁻¹ ξ) μW :=
        h0.congr (hae.mono fun x hx => by dsimp only; rw [(uw_inv hx).1])
      exact h0'.comp_fst
    exact h1.aestronglyMeasurable.smul (h2.aestronglyMeasurable.smul h3)
  have hFb : ∀ᵐ p ∂(μW.prod μN), ‖F p‖ ≤ ‖S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)‖ := haeP.mono fun p hp => by
    simp only [hF, chiInv, psiCoef, inv_one, Matrix.one_mul, Matrix.mul_one]
    rw [hPsi _ _ hp, norm_smul, norm_smul, norm_star, hψ, norm_psiGen, one_mul, hunit _ (hinvG _ hp), hξn, mul_one]
    have hA1 : ‖HW.torepSig T (P * Matrix.of p.1 * P⁻¹)‖ ≤ 1 :=
      opNorm_le_one_of_isometry_alt _ ((HW.torep_isURepOn T).2.1 _ (hK _ hp))
    calc ‖⟪T.w, (HW.torepSig T (P * Matrix.of p.1 * P⁻¹) * S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)) T.w⟫_ℂ‖
        ≤ ‖T.w‖ * ‖(HW.torepSig T (P * Matrix.of p.1 * P⁻¹) * S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)) T.w‖ :=
          norm_inner_le_norm _ _
      _ ≤ 1 * (‖HW.torepSig T (P * Matrix.of p.1 * P⁻¹) * S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)‖ * 1) := by
          rw [T.w_norm]
          gcongr
          calc _ ≤ _ := ContinuousLinearMap.le_opNorm _ _
            _ = _ := by rw [T.w_norm]
      _ ≤ ‖HW.torepSig T (P * Matrix.of p.1 * P⁻¹)‖ * ‖S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)‖ := by
          rw [one_mul, mul_one]; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)‖ := by gcongr
      _ = _ := one_mul _
  have hFi : Integrable F (μW.prod μN) := by
    have hφ : Integrable (fun p : Mt k r × Mt k r => ‖S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)‖) (μW.prod μN) := by
      have := (integrable_const (1 : ℝ) (μ := μW)).mul_prod hint
      simpa using this
    exact hφ.mono' hFm hFb
  rw [hA, ← integral_inner hFi ξ, integral_prod_symm _ (hFi.const_inner ξ)]
  have hin : ∀ m : Mt k r, ∫ h, ⟪ξ, F (h, m)⟫_ℂ ∂μW =
      (Module.finrank ℂ Vp : ℂ)⁻¹ * (psiCoef T μ P T.w T.w (Matrix.of m) * starRingEnd ℂ (ψ (Matrix.of m))) := by
    intro m
    have hpt : ∀ᵐ h ∂μW, ⟪ξ, F (h, m)⟫_ℂ = starRingEnd ℂ (ψ (Matrix.of m)) *
        (⟪ξ, π (Matrix.of h)⁻¹ ξ⟫_ℂ * ⟪T.w, HW.torepSig T (P * Matrix.of h * P⁻¹)
          (S7.PsiM T μ (P * Matrix.of m * P⁻¹) T.w)⟫_ℂ) := hae.mono fun h hh => by
      simp only [hF, chiInv, psiCoef, inv_one, Matrix.one_mul, Matrix.mul_one, inner_smul_right]
      have e : ∀ (A B : T.V →L[ℂ] T.V) (v : T.V), (A * B) v = A (B v) := fun _ _ _ => rfl
      rw [hPsi _ _ hh, e, show star (ψ (Matrix.of m)) = starRingEnd ℂ (ψ (Matrix.of m)) from rfl]
      ring
    rw [integral_congr_ae hpt, integral_const_mul, schur_orthogonality_whittaker T π hP hW hπ hξn hξ hΛ hμW hμ1]
    simp only [psiCoef]
    ring
  simp only [hin]
  rw [integral_const_mul]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
