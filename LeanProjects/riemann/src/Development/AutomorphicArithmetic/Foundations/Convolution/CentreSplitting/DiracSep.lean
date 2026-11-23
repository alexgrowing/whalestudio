import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
import GroundTheory.AutomorphicForms.L2LocalComponents.ArchBump
import GroundTheory.AutomorphicForms.CuspidalProjection.OrthogonalProjectionOntoCompSubtypeL

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

open scoped InnerProductSpace Topology

private theorem near_one_nhds {G H : Type*} [Group G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) {v : H} (hpos : 0 < ‖v‖) :
    {g : G | ‖π g v - v‖ < ‖v‖ / 2} ∈ 𝓝 (1 : G) := by
  have hcont : Continuous fun g => π g v := π.continuous_orbit v
  have ht : Filter.Tendsto (fun g => ‖π g v - v‖) (𝓝 (1 : G)) (𝓝 ‖π 1 v - v‖) :=
    (hcont.sub continuous_const).norm.tendsto 1
  rw [UnitaryRep.map_one_apply, sub_self, norm_zero] at ht
  exact ht.eventually_lt_const (half_pos hpos)

private theorem exists_bump_nonzero {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsHaarMeasure] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) {v : H} (hpos : 0 < ‖v‖) (ρ : G → ℝ) (β : CompactlySupportedContinuousMap G ℂ)
    (hβa : ∀ g, β g = (ρ g : ℂ)) (hρ0 : ∀ g, 0 ≤ ρ g) (hρ1 : ∫ g, ρ g ∂ν = 1)
    (hρN : ∀ g, ρ g ≠ 0 → g ∈ {g : G | ‖π g v - v‖ < ‖v‖ / 2})
    (h2 : π.integrated ν (UnitaryRep.ccToL1 ν β) v = 0) : False := by
  have hcont : Continuous fun g => π g v := π.continuous_orbit v
  have hin : ∫ g, (ρ g : ℂ) * ⟪v, π g v⟫_ℂ ∂ν = 0 := by
    have h1 := CuspidalProjection.inner_integrated_ccToL1 ν π β v v
    rw [h2, inner_zero_right] at h1
    simp only [hβa] at h1
    exact h1.symm
  have hρi : Integrable ρ ν := by
    by_contra h
    rw [integral_undef h] at hρ1
    exact zero_ne_one hρ1
  have hint : ∀ F : G → ℂ, Continuous F → Integrable (fun g => (ρ g : ℂ) * F g) ν := fun F hF => by
    simp only [← hβa]
    exact (β.continuous.mul hF).integrable_of_hasCompactSupport (β.hasCompactSupport.mul_right)
  have hc1 : Continuous fun g => ⟪v, π g v⟫_ℂ := continuous_const.inner hcont
  have e : ∫ g, (ρ g : ℂ) * ⟪v, π g v - v⟫_ℂ ∂ν = -⟪v, v⟫_ℂ := by
    have h3 : (fun g => (ρ g : ℂ) * ⟪v, π g v - v⟫_ℂ) =
        fun g => (ρ g : ℂ) * ⟪v, π g v⟫_ℂ - (ρ g : ℂ) * ⟪v, v⟫_ℂ := by
      funext g
      rw [inner_sub_right, mul_sub]
    rw [h3, integral_sub (hint _ hc1) (hint _ continuous_const), hin, integral_mul_const,
      integral_complex_ofReal, hρ1]
    simp
  have hb : ‖∫ g, (ρ g : ℂ) * ⟪v, π g v - v⟫_ℂ ∂ν‖ ≤ ∫ g, ρ g * (‖v‖ * (‖v‖ / 2)) ∂ν := by
    refine norm_integral_le_of_norm_le (hρi.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
    rcases eq_or_ne (ρ g) 0 with h0 | h0
    · simp [h0]
    · have hg : ‖π g v - v‖ < ‖v‖ / 2 := hρN g h0
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ0 g)]
      refine mul_le_mul_of_nonneg_left ?_ (hρ0 g)
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hg.le hpos.le)
  rw [e, integral_mul_const, hρ1, one_mul, norm_neg, inner_self_eq_norm_sq_to_K] at hb
  have h4 : ‖((‖v‖ : ℝ) : ℂ) ^ 2‖ = ‖v‖ ^ 2 := by simp
  have h5 : ‖v‖ ^ 2 ≤ ‖v‖ * (‖v‖ / 2) := by
    rw [← h4]
    simpa using hb
  nlinarith

theorem UpperTheory.ConvolutionTheory.Dp.diracSep :
    UpperTheory.ConvolutionTheory.Dp.DiracSep := by
  intro K _ _ n μ _ ν _ v hv
  by_contra hne
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hne
  obtain ⟨ρ, hρ0, hρt, hρ1, -, -, hρN, -⟩ := exists_archBump ν
    (near_one_nhds ((rightRegularRep (rationalGLOne K n) μ).compHom (archP K n) continuous_archP) hpos)
  let β : TI K n := ⟨⟨fun a => (ρ a : ℂ), hρt.continuous _⟩, hρt.2⟩
  exact exists_bump_nonzero ν _ hpos ρ β (fun _ => rfl) hρ0 hρ1 hρN (hv β hρt.1)
