import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleCpowDetInverseTwist

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem integrableOn_Zg_integrand {μ : Measure G2} {𝓕 : Set G2} {H : G2 → ℂ}
    {Φ : (Fin 2 → 𝔸[ℚ]) → ℂ} (c : HeckeCharacter ℚ) (hH : Aut H) (s : ℂ)
    (mth : Measurable (th Φ))
    (fin : ∫⁻ g in 𝓕, (‖H g‖ₑ * ENNReal.ofReal (Dt g ^ s.re)) * ∑' ξ : NZ, ‖Φ (row ξ.1 g)‖ₑ ∂μ < ∞) :
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g) 𝓕 μ := by
  refine ⟨((measurable_w hH c s).mul mth).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) fin
  have h1 : ‖cdet c g‖ₑ = 1 := by
    rw [← ofReal_norm_eq_enorm, norm_cdet]; simp
  have h2 : ‖((Dt g : ℝ) : ℂ) ^ s‖ₑ = ENNReal.ofReal (Dt g ^ s.re) := by
    rw [← ofReal_norm_eq_enorm, Complex.norm_cpow_eq_rpow_re_of_pos (Dt_pos g)]
  have h3 : ‖th Φ g‖ₑ ≤ ∑' ξ : NZ, ‖Φ (row ξ.1 g)‖ₑ := enorm_tsum_le_tsum_enorm
  simp only [enorm_mul, h1, h2, mul_one]
  gcongr

theorem integrand_theta_eq {H : G2 → ℂ} {Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ} (c : HeckeCharacter ℚ) (s : ℂ) (g : G2)
    (hth : th Φ g + Φ 0 = (((Dt g)⁻¹ : ℝ) : ℂ) * (th Φ' (inv2 g) + Φ' 0)) :
    H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g =
      H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1) * th Φ' (inv2 g)
        + Φ' 0 * (H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1))
        - Φ 0 * (H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) := by
  have hD := Dt_ne g
  have hp : ((Dt g : ℝ) : ℂ) ^ (s - 1) = ((Dt g : ℝ) : ℂ) ^ s * (((Dt g)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.cpow_sub _ _ hD, Complex.cpow_one, Complex.ofReal_inv, div_eq_mul_inv]
  have ht : th Φ g = (((Dt g)⁻¹ : ℝ) : ℂ) * (th Φ' (inv2 g) + Φ' 0) - Φ 0 := by
    rw [← hth]; ring
  rw [hp, ht]; ring

theorem setIntegral_lower_det_inverse_twist {μ : Measure G2} {𝓕 : Set G2} {H : G2 → ℂ}
    {Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ} (c : HeckeCharacter ℚ) (hH : Aut H) (s : ℂ)
    (hm : MeasurableSet 𝓕) (hnull : μ {g | Dt g = 1} = 0)
    (hT : ∀ F : G2 → ℂ, Measurable F → LInv F → ∫ g in 𝓕, F (inv2 g) ∂μ = ∫ g in 𝓕, F g ∂μ)
    (mth : Measurable (th Φ')) (lth : LInv (th Φ')) :
    ∫ g in 𝓕 ∩ {g | Dt g < 1}, H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1) * th Φ' (inv2 g) ∂μ =
      Zp μ 𝓕 H c⁻¹ Φ' (1 - s) := by
  have hB : MeasurableSet {g | Dt g < 1} := measurableSet_lt measurable_Dt measurable_const
  have hC : MeasurableSet {g | Dt g ∈ Set.Ioi (1 : ℝ)} := measurable_Dt measurableSet_Ioi
  set G : G2 → ℂ := fun g => H g * cdet c⁻¹ g * ((Dt g : ℝ) : ℂ) ^ (1 - s) * th Φ' g with hG
  have mG : Measurable G := (measurable_w hH c⁻¹ (1 - s)).mul mth
  have lG : LInv G := fun γ g => by
    have := linv_w hH c⁻¹ (1 - s) γ g
    simp only [hG, lth γ g]
    simp only at this
    rw [this]
  have key := hT _ (mG.indicator hC) (linv_ind lG (Set.Ioi (1 : ℝ)))
  have hpt : ∀ g, Set.indicator {g | Dt g ∈ Set.Ioi (1 : ℝ)} G (inv2 g) =
      Set.indicator {g | Dt g < 1} (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1) * th Φ' (inv2 g)) g := by
    intro g
    have hiff : inv2 g ∈ {g | Dt g ∈ Set.Ioi (1 : ℝ)} ↔ g ∈ {g | Dt g < 1} := by
      simp only [Set.mem_setOf_eq, Set.mem_Ioi, module_det_inverse_twist]
      exact one_lt_inv₀ (Dt_pos g)
    by_cases h : g ∈ {g | Dt g < 1}
    · rw [Set.indicator_of_mem (hiff.2 h), Set.indicator_of_mem h]
      simp only [hG, character_det_inverse_twist, inv_inv, module_cpow_det_inverse_twist, Aut.inv2 hH, neg_sub]
    · rw [Set.indicator_of_notMem (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h]
  simp only [hpt] at key
  rw [setIntegral_indicator hB, setIntegral_indicator hC] at key
  rw [key]
  refine setIntegral_congr_set ?_
  have hae : ∀ᵐ g ∂μ, Dt g ≠ 1 := by
    have : μ ({g | Dt g ≠ 1}ᶜ) = 0 := by
      convert hnull using 2
      ext g; simp
    exact this
  refine Filter.eventuallyEq_set.2 ?_
  filter_upwards [hae] with g hg
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ioi]
  exact and_congr_right fun _ => ⟨fun h => h.le, fun h => lt_of_le_of_ne h (Ne.symm hg)⟩

theorem Zg_decomposition : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G1a → Ad3.R.G3 → Set0 μ 𝓕 mK 𝓓 → Aut H → Φ ∈ Adele2.schwartzBruhat2 ℚ → Φ' ∈ Adele2.schwartzBruhat2 ℚ →
  (∀ g, th Φ g + Φ 0 = (((Dt g)⁻¹ : ℝ) : ℂ) * (th Φ' (inv2 g) + Φ' 0)) →
  (∀ t : ℂ, 0 < t.re → IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ t) (𝓕 ∩ {g | Dt g < 1}) μ) →
  ∀ s : ℂ, 1 < s.re → Zg μ 𝓕 H c Φ s = GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c Φ s + GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c⁻¹ Φ' (1 - s)
    + Φ' 0 * GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c (s - 1) - Φ 0 * GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s := by
  intro μ 𝓕 mK 𝓓 H Φ Φ' c h1 h3 h0 hH hΦ hΦ' hth hw s hs
  obtain ⟨mth, -, fin⟩ := h3 μ 𝓕 mK 𝓓 h0 H hH Φ hΦ s.re hs
  obtain ⟨mth', lth', -⟩ := h3 μ 𝓕 mK 𝓓 h0 H hH Φ' hΦ' 2 (by norm_num)
  obtain ⟨hnull, -, hT⟩ := h1 μ 𝓕 mK 𝓓 h0
  have hWi := integrableOn_Zg_integrand c hH s mth fin
  have hA : MeasurableSet {g | 1 ≤ Dt g} := measurableSet_le measurable_const measurable_Dt
  have hinv := setIntegral_lower_det_inverse_twist (Φ' := Φ') c hH s h0.meas hnull
    (fun F mF lF => (hT inv2 (Or.inl rfl)).2 F mF lF) mth' lth'
  have hw1 := hw (s - 1) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  have hw2 := hw s (by linarith)
  have hWB : IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g)
      (𝓕 ∩ {g | Dt g < 1}) μ := hWi.mono_set Set.inter_subset_left
  have hpt := fun g => integrand_theta_eq (H := H) c s g (hth g)
  have hVi : IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1) * th Φ' (inv2 g))
      (𝓕 ∩ {g | Dt g < 1}) μ := by
    have := (hWB.sub (hw1.const_mul (Φ' 0))).add (hw2.const_mul (Φ 0))
    refine this.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, hpt g]
    ring
  have hsplit : Zg μ 𝓕 H c Φ s = Zp μ 𝓕 H c Φ s +
      ∫ g in 𝓕 ∩ {g | Dt g < 1}, H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g ∂μ := by
    have hd : 𝓕 \ {g | 1 ≤ Dt g} = 𝓕 ∩ {g | Dt g < 1} := by
      ext g; simp
    rw [← hd]
    exact (integral_inter_add_diff hA hWi).symm
  have hB : ∫ g in 𝓕 ∩ {g | Dt g < 1}, H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g ∂μ =
      Zp μ 𝓕 H c⁻¹ Φ' (1 - s) + Φ' 0 * Jl μ 𝓕 H c (s - 1) - Φ 0 * Jl μ 𝓕 H c s := by
    have i1 : Integrable (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1) * th Φ' (inv2 g)
        + Φ' 0 * (H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1))) (μ.restrict (𝓕 ∩ {g | Dt g < 1})) :=
      hVi.add (hw1.const_mul _)
    simp only [hpt]
    rw [integral_sub i1 (hw2.const_mul _), integral_add hVi (hw1.const_mul _),
      integral_const_mul, integral_const_mul, hinv, Jl, Jl]
  rw [hsplit, hB]; ring

end GlobalTheory.CompanionTheory.RSZeta
