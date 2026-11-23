import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarCompactLtTop
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf

theorem ballMean_eLpNorm_two_le {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {ν : Measure α} {f : α → E} {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (h : ∫⁻ x, (‖f x‖₊ : ENNReal) ^ 2 ∂ν ≤ ENNReal.ofReal (C * a ^ 2)) :
    eLpNorm f 2 ν ≤ ENNReal.ofReal (Real.sqrt C * a) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (∫⁻ x, ‖f x‖ₑ ^ (ENNReal.toReal 2) ∂ν) = ∫⁻ x, (‖f x‖₊ : ENNReal) ^ 2 ∂ν := by
    congr 1; funext x
    rw [show ENNReal.toReal 2 = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    rfl
  rw [h2]
  calc _ ≤ (ENNReal.ofReal (C * a ^ 2)) ^ (1 / (ENNReal.toReal 2)) := by gcongr
    _ = ENNReal.ofReal (Real.sqrt C * a) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      congr 1
      rw [show (1 / ENNReal.toReal 2 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
        Real.sqrt_mul' _ (by positivity), Real.sqrt_sq ha]

theorem ballMean_norm_integral_le {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ν : Measure α} [IsFiniteMeasure ν] {f : α → E} {C a : ℝ} (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hf : AEStronglyMeasurable f ν)
    (h : ∫⁻ x, (‖f x‖₊ : ENNReal) ^ 2 ∂ν ≤ ENNReal.ofReal (C * a ^ 2)) :
    Integrable f ν ∧ ‖∫ x, f x ∂ν‖ ≤ Real.sqrt C * (ν Set.univ).toReal ^ (1 / 2 : ℝ) * a := by
  have h2 := ballMean_eLpNorm_two_le hC ha h
  have hL2 : MemLp f 2 ν := ⟨hf, lt_of_le_of_lt h2 ENNReal.ofReal_lt_top⟩
  refine ⟨hL2.integrable (by norm_num), ?_⟩
  have h1 : eLpNorm f 1 ν ≤ eLpNorm f 2 ν * ν Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hf
  rw [eLpNorm_one_eq_lintegral_enorm] at h1
  have hexp : (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal : ℝ) = 1 / 2 := by norm_num
  rw [hexp] at h1
  have hmu : ν Set.univ ^ (1 / 2 : ℝ) = ENNReal.ofReal ((ν Set.univ).toReal ^ (1 / 2 : ℝ)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal (measure_ne_top ν _)]
  have key : ‖∫ x, f x ∂ν‖ₑ ≤ ENNReal.ofReal (Real.sqrt C * (ν Set.univ).toReal ^ (1 / 2 : ℝ) * a) := by
    calc ‖∫ x, f x ∂ν‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ ≤ eLpNorm f 2 ν * ν Set.univ ^ (1 / 2 : ℝ) := h1
      _ ≤ ENNReal.ofReal (Real.sqrt C * a) * ENNReal.ofReal ((ν Set.univ).toReal ^ (1 / 2 : ℝ)) := by
          rw [hmu]; gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  rw [← ofReal_norm_eq_enorm] at key
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key

theorem ballMean_clm : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (T : H → Mat k r → Wp), IsHaarOn (GG k r) μG →
    (∀ u u' : H, (fun x : Mt k r => T (u + u') (Matrix.of x)) =ᵐ[μG]
      fun x => T u (Matrix.of x) + T u' (Matrix.of x)) →
    (∀ (b : ℂ) (u : H), (fun x : Mt k r => T (b • u) (Matrix.of x)) =ᵐ[μG] fun x => b • T u (Matrix.of x)) →
    (∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u : H,
      AEStronglyMeasurable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict K) ∧
      ∫⁻ x in K, (‖T u (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ y ∈ GG k r, ∀ u : H, (fun x : Mt k r => T (σ y u) (Matrix.of x)) =ᵐ[μG]
      fun x => T u (Matrix.of x * y)) →
    ∀ j : ℕ, ∃ Λ : H →L[ℂ] Wp, ∀ (v : H) (x : Mt k r), Matrix.of x ∈ GG k r →
      Λ (σ (Matrix.of x) v) = avgR μG j (fun z : Mt k r => T v (Matrix.of z)) x := by
  intro k r H _ _ _ Wp _ _ _ σ μG T hμ hadd hsmul hL2 htr j
  have hBfin : μG (nbd k r j) < ⊤ := haar_compact_lt_top hμ (isCompact_nbd j)
  haveI : IsFiniteMeasure (μG.restrict (nbd k r j)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hBfin⟩
  obtain ⟨C, hC⟩ := hL2 (nbd k r j) (isCompact_nbd j)
  have hb : ∀ u : H, Integrable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict (nbd k r j)) ∧
      ‖∫ x in nbd k r j, T u (Matrix.of x) ∂μG‖ ≤
        Real.sqrt (max C 0) * ((μG.restrict (nbd k r j)) Set.univ).toReal ^ (1 / 2 : ℝ) * ‖u‖ := by
    intro u
    refine ballMean_norm_integral_le (le_max_right C 0) (norm_nonneg u) (hC u).1 ?_
    refine (hC u).2.trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    exact le_max_left C 0
  set c : ℝ := ((μG (nbd k r j)).toReal)⁻¹ with hc
  have hc0 : 0 ≤ c := inv_nonneg.2 ENNReal.toReal_nonneg
  let L : H →ₗ[ℂ] Wp :=
    { toFun := fun v => c • ∫ x in nbd k r j, T v (Matrix.of x) ∂μG
      map_add' := fun u u' => by
        rw [integral_congr_ae (ae_restrict_of_ae (hadd u u')), integral_add (hb u).1 (hb u').1, smul_add]
      map_smul' := fun b u => by
        simp only [RingHom.id_apply]
        rw [integral_congr_ae (ae_restrict_of_ae (hsmul b u)), integral_smul, smul_comm] }
  refine ⟨L.mkContinuous (c * (Real.sqrt (max C 0) *
      ((μG.restrict (nbd k r j)) Set.univ).toReal ^ (1 / 2 : ℝ))) ?_, ?_⟩
  · intro v
    show ‖c • ∫ x in nbd k r j, T v (Matrix.of x) ∂μG‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg hc0, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb v).2 hc0
  · intro v x hx
    show c • ∫ y in nbd k r j, T (σ (Matrix.of x) v) (Matrix.of y) ∂μG = _
    unfold avgR
    rw [integral_congr_ae (ae_restrict_of_ae (htr _ hx v))]
    rfl

end GlobalTheory.SgInf
