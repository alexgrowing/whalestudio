import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

namespace DiscreteGroups.T1.G

variable (X : Ctx)

theorem enorm_conj' (a : ℂ) : ‖starRingEnd ℂ a‖ₑ = ‖a‖ₑ := by
  rw [← ofReal_norm_eq_enorm, Complex.norm_conj, ofReal_norm_eq_enorm]

theorem tst_norm {φ : X.G → ℂ} (hφ : Tst φ) : Tst (fun w => ((‖φ w‖ : ℝ) : ℂ)) :=
  ⟨Complex.continuous_ofReal.comp hφ.1.norm,
    hφ.2.mono' (fun w hw => subset_tsupport _ (by simpa [Function.mem_support] using hw))⟩

theorem aesm_of_inv {f : X.G → ℂ} (hinv : ∀ γ : X.Γ, ∀ y, f ((γ : X.G) * y) = f y)
    (hf : AEStronglyMeasurable f X.ν) : AEStronglyMeasurable f X.μ := by
  have hU : (⋃ γ : X.Γ, γ • X.F) =ᵐ[X.μ] (Set.univ : Set X.G) := X.fd.iUnion_smul_ae_eq
  have hμ : X.μ = X.μ.restrict (⋃ γ : X.Γ, γ • X.F) := by
    rw [Measure.restrict_congr_set hU, Measure.restrict_univ]
  rw [hμ, aestronglyMeasurable_iUnion_iff]
  intro γ
  have hmp : MeasurePreserving (fun y : X.G => (γ : X.G)⁻¹ * y) (X.μ.restrict (γ • X.F)) X.ν := by
    have h0 : MeasurePreserving (fun y : X.G => (γ : X.G)⁻¹ * y) X.μ X.μ := measurePreserving_mul_left X.μ _
    have h1 := h0.restrict_preimage_emb (MeasurableEquiv.mulLeft ((γ : X.G)⁻¹)).measurableEmbedding X.F
    have h2 : (fun y : X.G => (γ : X.G)⁻¹ * y) ⁻¹' X.F = γ • X.F := by
      ext y
      simp [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
    rw [h2] at h1
    exact h1
  refine (hf.comp_measurePreserving hmp).congr (Filter.Eventually.of_forall fun y => ?_)
  have := hinv γ⁻¹ y
  simpa using this

theorem lint_rt (hr : X.μ.IsMulRightInvariant) {g : X.G → ℝ≥0∞}
    (hinv : ∀ γ : X.Γ, ∀ y, g ((γ : X.G) * y) = g y) (z : X.G) :
    ∫⁻ x, g (x * z) ∂X.ν = ∫⁻ x, g x ∂X.ν := by
  have hmp : MeasurePreserving (fun y : X.G => y * z⁻¹) X.μ X.μ := measurePreserving_mul_right X.μ _
  have hfd : IsFundamentalDomain X.Γ ((fun y : X.G => y * z⁻¹) ⁻¹' X.F) X.μ :=
    X.fd.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id
      (fun γ y => by simp [Subgroup.smul_def, mul_assoc])
  have h1 : ∫⁻ x in X.F, g (x * z) ∂X.μ = ∫⁻ y in (fun y : X.G => y * z⁻¹) ⁻¹' X.F, g y ∂X.μ := by
    rw [← hmp.setLIntegral_comp_preimage_emb (MeasurableEquiv.mulRight z⁻¹).measurableEmbedding
      (fun x => g (x * z)) X.F]
    simp
  show ∫⁻ x in X.F, g (x * z) ∂X.μ = ∫⁻ x in X.F, g x ∂X.μ
  rw [h1, hfd.setLIntegral_eq X.fd g (fun γ y => by simpa [Subgroup.smul_def] using hinv γ y)]

end DiscreteGroups.T1.G

end
