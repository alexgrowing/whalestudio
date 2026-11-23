import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

noncomputable section

open MeasureTheory

namespace PositivityTheory.RgDs.K

theorem equivariant_section_holds : EquivSection := by
  intro G _ _ _ _ _ _ _ A S _ _ _ _ _ _ ρ σ hρ1 hρm hρc hσ1 hσm hσc f hf hfe
  obtain ⟨s0, hs0⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  have hs0y : ∀ y, f (s0 y) = y := fun y => by
    simpa using congrArg (fun T : S →ₗ[ℂ] S => T y) hs0
  have hσmul : ∀ a b y, σ (a * b) y = σ a (σ b y) := fun a b y => by rw [hσm]; rfl
  have hρmul : ∀ a b x, ρ (a * b) x = ρ a (ρ b x) := fun a b x => by rw [hρm]; rfl
  have hσinv : ∀ g y, σ g (σ g⁻¹ y) = y := fun g y => by
    rw [← hσmul, mul_inv_cancel, hσ1]; rfl
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure G, μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  let F : S → G → A := fun y g => ρ g (s0 (σ g⁻¹ y))
  have hFc : ∀ y, Continuous (F y) := fun y =>
    hρc.clm_apply ((LinearMap.continuous_of_finiteDimensional s0).comp ((hσc y).comp continuous_inv))
  have hFi : ∀ y, Integrable (F y) μ := fun y =>
    integrableOn_univ.mp ((hFc y).continuousOn.integrableOn_compact isCompact_univ)
  have hFadd : ∀ x y, F (x + y) = F x + F y := fun x y => by
    funext g; simp [F]
  have hFsmul : ∀ (r : ℂ) y, F (r • y) = r • F y := fun r y => by
    funext g; simp [F]
  set c : ℝ := μ.real Set.univ with hc_def
  have hc : c ≠ 0 := by
    rw [hc_def, Measure.real]
    exact ENNReal.toReal_ne_zero.mpr ⟨isOpen_univ.measure_ne_zero μ Set.univ_nonempty, measure_ne_top μ _⟩
  let s : S →ₗ[ℂ] A :=
    { toFun := fun y => ((c : ℂ)⁻¹) • ∫ g, F y g ∂μ
      map_add' := fun x y => by
        simp only [hFadd]
        rw [Pi.add_def, integral_add (hFi x) (hFi y), smul_add]
      map_smul' := fun r y => by
        simp only [hFsmul, RingHom.id_apply]
        rw [Pi.smul_def, integral_smul, smul_comm] }
  refine ⟨s, fun y => ?_, fun h y => ?_⟩
  · let fL : A →L[ℂ] S := LinearMap.toContinuousLinearMap f
    have h1 : f (∫ g, F y g ∂μ) = ∫ g, fL (F y g) ∂μ :=
      (fL.integral_comp_comm (hFi y)).symm
    have h2 : ∀ g, fL (F y g) = y := fun g => by
      show f (ρ g (s0 (σ g⁻¹ y))) = y
      rw [hfe, hs0y, hσinv]
    show f (((c : ℂ)⁻¹) • ∫ g, F y g ∂μ) = y
    rw [map_smul, h1]
    simp only [h2, integral_const]
    rw [← hc_def, ← Complex.coe_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hc), one_smul]
  · have h3 : ∀ g, F (σ h y) (h * g) = ρ h (F y g) := fun g => by
      show ρ (h * g) (s0 (σ (h * g)⁻¹ (σ h y))) = ρ h (ρ g (s0 (σ g⁻¹ y)))
      rw [hρmul, mul_inv_rev, hσmul, ← hσmul h⁻¹ h, inv_mul_cancel, hσ1]; rfl
    have h4 : ∫ g, F (σ h y) g ∂μ = ρ h (∫ g, F y g ∂μ) := by
      rw [← integral_mul_left_eq_self (F (σ h y)) h]
      simp only [h3]
      exact (ρ h).integral_comp_comm (hFi y)
    show ((c : ℂ)⁻¹) • ∫ g, F (σ h y) g ∂μ = ρ h (((c : ℂ)⁻¹) • ∫ g, F y g ∂μ)
    rw [h4, map_smul]

end PositivityTheory.RgDs.K
