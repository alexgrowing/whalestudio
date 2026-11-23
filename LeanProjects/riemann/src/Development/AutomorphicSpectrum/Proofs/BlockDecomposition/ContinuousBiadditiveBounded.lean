import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Arch

theorem continuous_biadditive_bounded :
    ∀ (N₁ N₂ N₃ : ℕ) (β : (Fin N₁ → ℝ) → (Fin N₂ → ℝ) → (Fin N₃ → ℝ)),
      (∀ u u' v, β (u + u') v = β u v + β u' v) →
      (∀ u v v', β u (v + v') = β u v + β u v') →
      Continuous (fun p : (Fin N₁ → ℝ) × (Fin N₂ → ℝ) => β p.1 p.2) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u v, ‖β u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  intro N₁ N₂ N₃ β h₁ h₂ hβ
  have smul₁ : ∀ (c : ℝ) u v, β (c • u) v = c • β u v := by
    intro c u v
    exact map_real_smul (AddMonoidHom.mk' (fun u => β u v) fun u u' => h₁ u u' v)
      (hβ.comp (continuous_id.prodMk continuous_const)) c u
  have smul₂ : ∀ (c : ℝ) u v, β u (c • v) = c • β u v := by
    intro c u v
    exact map_real_smul (AddMonoidHom.mk' (fun v => β u v) fun v v' => h₂ u v v')
      (hβ.comp (continuous_const.prodMk continuous_id)) c v
  have zero₁ : ∀ v, β 0 v = 0 := fun v => by simpa using smul₁ 0 0 v
  have zero₂ : ∀ u, β u 0 = 0 := fun u => by simpa using smul₂ 0 u 0
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuous_iff.mp hβ 0 1 one_pos
  have key : ∀ u v, ‖u‖ < δ → ‖v‖ < δ → ‖β u v‖ < 1 := by
    intro u v hu hv
    have h := hsmall (u, v) (by rw [dist_zero_right, Prod.norm_def]; exact max_lt hu hv)
    simpa [zero₁, dist_zero_right] using h
  obtain ⟨s, rfl⟩ : ∃ s, δ = 2 * s := ⟨δ / 2, by ring⟩
  have hs0 : 0 < s := by linarith
  have hsδ : s < 2 * s := by linarith
  refine ⟨4 / (2 * s) ^ 2, by positivity, fun u v => ?_⟩
  by_cases hu : u = 0
  · simp [hu, zero₁]
  by_cases hv : v = 0
  · simp [hv, zero₂]
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnu : ‖(s / ‖u‖) • u‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg (div_pos hs0 hu').le]
    field_simp
  have hnv : ‖(s / ‖v‖) • v‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg (div_pos hs0 hv').le]
    field_simp
  have hb := key ((s / ‖u‖) • u) ((s / ‖v‖) • v) (by rw [hnu]; exact hsδ) (by rw [hnv]; exact hsδ)
  rw [smul₁, smul₂, smul_smul, norm_smul,
    Real.norm_of_nonneg (mul_pos (div_pos hs0 hu') (div_pos hs0 hv')).le] at hb
  have e : s / ‖u‖ * (s / ‖v‖) * ‖β u v‖ = (‖β u v‖ * (s * s)) / (‖u‖ * ‖v‖) := by ring
  rw [e, div_lt_one (mul_pos hu' hv')] at hb
  rw [show 4 / (2 * s) ^ 2 * ‖u‖ * ‖v‖ = (‖u‖ * ‖v‖) / (s * s) by ring,
    le_div_iff₀ (mul_pos hs0 hs0)]
  exact hb.le

end GlobalTheory.CompanionTheory.Arch
