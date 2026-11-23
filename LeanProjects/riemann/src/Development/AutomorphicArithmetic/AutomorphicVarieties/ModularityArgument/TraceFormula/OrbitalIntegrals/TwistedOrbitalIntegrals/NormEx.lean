import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.normEx :
    UpperTheory.V.Z.Tf.Orb.NormEx := by
  classical
  intro G _ _ _ _ _ _ _ _ ⟨K, hKo, hKc⟩ H hH μ hμ hr
  let r : G → G := fun g => (DoubleCoset.mk H K g).out
  have hr1 : ∀ g, ∃ h ∈ H, ∃ k ∈ K, r g = h * g * k := fun g => by
    obtain ⟨h, k, hh, hk, e⟩ := DoubleCoset.mk_out_eq_mul H K g
    exact ⟨h, hh, k, hk, e⟩
  have hr2 : ∀ h ∈ H, ∀ g, ∀ k ∈ K, r (h * g * k) = r g := fun h hh g k hk =>
    congrArg Quotient.out ((DoubleCoset.eq H K _ _).2 ⟨h, hh, k, hk, rfl⟩).symm
  let A : G → Set H := fun x => {h | x⁻¹ * h * x ∈ K}
  have hAo : ∀ x, IsOpen (A x) := fun x => hKo.preimage (by fun_prop)
  have hAc : ∀ x, IsCompact (A x) := fun x => by
    have h1 : IsCompact ((fun z => x⁻¹ * z * x) ⁻¹' (K : Set G)) :=
      ((Homeomorph.mulLeft x⁻¹).trans (Homeomorph.mulRight x)).isCompact_preimage.2 hKc
    exact hH.isClosedEmbedding_subtypeVal.isCompact_preimage h1
  have h0 : ∀ x, μ (A x) ≠ 0 := fun x => ((hAo x).measure_pos μ ⟨1, by simp [A, K.one_mem]⟩).ne'
  have ht : ∀ x, μ (A x) ≠ ∞ := fun x => (hAc x).measure_lt_top.ne
  let ρ : G → ℝ≥0∞ := fun g => if (r g)⁻¹ * g ∈ K then (μ (A (r g)))⁻¹ else 0
  have hk : ∀ g, ∀ k ∈ K, ρ (g * k) = ρ g := fun g k hk => by
    have : r (g * k) = r g := by simpa using hr2 1 H.one_mem g k hk
    simp only [ρ, this, ← mul_assoc, K.mul_mem_cancel_right hk]
  have hlc : IsLocallyConstant ρ := (IsLocallyConstant.iff_exists_open ρ).2 fun g =>
    ⟨(fun z => g⁻¹ * z) ⁻¹' K, hKo.preimage (by fun_prop), by simp [K.one_mem], fun z hz => by
      rw [← hk g _ hz, mul_inv_cancel_left]⟩
  refine ⟨ρ, ⟨hlc.continuous.measurable, fun g => ?_⟩, fun g => ?_⟩
  · obtain ⟨h₀, hh, k, hk', e⟩ := hr1 g
    have e1 : ∀ h : H, ρ (h * g) = (A (r g)).indicator (fun _ => (μ (A (r g)))⁻¹) (h * (⟨h₀, hh⟩ : H)⁻¹) := fun h => by
      have h1 : r (h * g) = r g := by simpa using hr2 h h.2 g 1 K.one_mem
      have h2 : (r g)⁻¹ * (h * g) ∈ K ↔ h * (⟨h₀, hh⟩ : H)⁻¹ ∈ A (r g) := by
        rw [← K.mul_mem_cancel_right hk']
        change _ ↔ (r g)⁻¹ * ((h : G) * h₀⁻¹) * r g ∈ K
        have : (r g)⁻¹ * ((h : G) * h₀⁻¹) * r g = (r g)⁻¹ * (h * g) * k := by
          nth_rewrite 2 [e]
          group
        rw [this]
      simp only [ρ, h1, Set.indicator, h2]
    rw [lintegral_congr e1, lintegral_mul_right_eq_self, lintegral_indicator_const (hAo _).measurableSet,
      ENNReal.inv_mul_cancel (h0 _) (ht _)]
  · simp only [ρ]
    split_ifs
    · exact ENNReal.inv_ne_top.2 (h0 _)
    · exact ENNReal.zero_ne_top
