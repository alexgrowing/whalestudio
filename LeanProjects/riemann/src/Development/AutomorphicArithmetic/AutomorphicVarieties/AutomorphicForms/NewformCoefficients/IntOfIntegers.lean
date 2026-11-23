import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat

open NumberField IsDedekindDomain GlobalTheory.CuspRep

namespace UpperTheory.V.Af.Nf

private theorem memO {x : Af ℚ} :
    x ∈ Ohat ℚ ↔ ∀ v : HeightOneSpectrum (𝓞 ℚ), x v ∈ v.adicCompletionIntegers ℚ := by
  rw [Ohat, Subring.mem_iInf]
  rfl

private theorem int_of_integers (x : 𝓞 ℚ) : ∃ n : ℤ, (x : ℚ) = n :=
  ⟨Rat.ringOfIntegersEquiv x, (Rat.ringOfIntegersEquiv_apply_coe x).symm⟩

private theorem dense_int (M : ℕ) (hM : 1 ≤ M) (x : Af ℚ) (hx : x ∈ Ohat ℚ) :
    ∃ d : ℤ, ∃ y ∈ Ohat ℚ, x - d = M * y := by
  obtain ⟨r, a, ha, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat ℚ M hM).2 x (memO.1 hx)
  obtain ⟨n, hn⟩ := int_of_integers r
  refine ⟨n, a, memO.2 ha, ?_⟩
  rw [e, hn, map_intCast, nsmul_eq_mul]
  ring

private theorem exists_den (y : Af ℚ) : ∃ N : ℕ, 1 ≤ N ∧ (N : Af ℚ) * y ∈ Ohat ℚ := by
  obtain ⟨r, a, ha, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat ℚ 1 one_pos).1 y
  refine ⟨r.den, r.den_pos, ?_⟩
  have h : (r.den : Af ℚ) * algebraMap ℚ (Af ℚ) r = (r.num : Af ℚ) := by
    rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, Rat.den_mul_eq_num, map_intCast]
  rw [e, mul_add, h, one_smul]
  exact add_mem (intCast_mem _ _) (mul_mem (natCast_mem _ _) (memO.2 ha))

private theorem class_one (y : (Af ℚ)ˣ) : ∃ (r : ℚˣ) (u : (Af ℚ)ˣ), 0 < (r : ℚ) ∧ IsZU u ∧
    y = Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r * u := by
  classical
  obtain ⟨N, hN, ha⟩ := exists_den (y : Af ℚ)
  obtain ⟨M, hM, hb⟩ := exists_den ((y⁻¹ : (Af ℚ)ˣ) : Af ℚ)
  set a : Af ℚ := N * y with ha'
  set b : Af ℚ := M * ((y⁻¹ : (Af ℚ)ˣ) : Af ℚ) with hb'
  have hab : a * b = ((N * M : ℕ) : Af ℚ) := by
    rw [ha', hb', mul_mul_mul_comm, Units.mul_inv, mul_one, Nat.cast_mul]
  let I : Ideal ℤ :=
    { carrier := {n | ∃ w ∈ Ohat ℚ, (n : Af ℚ) = a * w}
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      add_mem' := by
        rintro m n ⟨w, hw, e⟩ ⟨w', hw', e'⟩
        exact ⟨w + w', add_mem hw hw', by rw [Int.cast_add, e, e', mul_add]⟩
      smul_mem' := by
        rintro c n ⟨w, hw, e⟩
        exact ⟨c * w, mul_mem (intCast_mem _ _) hw, by rw [smul_eq_mul, Int.cast_mul, e]; ring⟩ }
  obtain ⟨d₀, hd₀⟩ := (IsPrincipalIdealRing.principal I).principal
  have hI : I = Ideal.span {|d₀|} := by
    rw [hd₀, Ideal.submodule_span_eq, Ideal.span_singleton_abs]
  set d : ℤ := |d₀| with hd
  have hL : ((N * M : ℕ) : ℤ) ∈ I := ⟨b, hb, by rw [hab, Int.cast_natCast]⟩
  obtain ⟨w, hw, hdw⟩ : d ∈ I := hI ▸ Ideal.mem_span_singleton_self d
  obtain ⟨n, z, hz, hn⟩ := dense_int (N * M) (Nat.mul_pos hN hM) a ha
  have hnI : n ∈ I := ⟨1 - b * z, sub_mem (one_mem _) (mul_mem hb hz), by
    rw [← hab] at hn; linear_combination -hn⟩
  rw [hI, Ideal.mem_span_singleton] at hL hnI
  obtain ⟨l, hl⟩ := hL
  obtain ⟨k, hk⟩ := hnI
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, zero_mul, Nat.cast_eq_zero] at hl
    exact (Nat.mul_pos hN hM).ne' hl
  have hdpos : (0 : ℚ) < d := by exact_mod_cast lt_of_le_of_ne (abs_nonneg d₀) hd0.symm
  have hNpos : (0 : ℚ) < N := by exact_mod_cast hN
  have hl' : ((N * M : ℕ) : Af ℚ) = d * l := by
    rw [← Int.cast_natCast, hl, Int.cast_mul]
  have hau : a = d * ((k : Af ℚ) + l * z) := by
    rw [hk, hl', Int.cast_mul] at hn
    linear_combination hn
  have hdi : algebraMap ℚ (Af ℚ) (d : ℚ)⁻¹ * d = 1 := by
    rw [← map_intCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hdpos.ne', map_one]
  have hNi : algebraMap ℚ (Af ℚ) (N : ℚ)⁻¹ * N = 1 := by
    rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hNpos.ne', map_one]
  have huw : ((k : Af ℚ) + l * z) * w = 1 := by
    rw [hau] at hdw
    linear_combination (-algebraMap ℚ (Af ℚ) (d : ℚ)⁻¹) * hdw + (1 - ((k : Af ℚ) + l * z) * w) * hdi
  refine ⟨Units.mk0 (d / N) (div_pos hdpos hNpos).ne', ⟨(k : Af ℚ) + l * z, w, huw, by rw [mul_comm, huw]⟩,
    div_pos hdpos hNpos, ⟨add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) hz), hw⟩, Units.ext ?_⟩
  change (y : Af ℚ) = algebraMap ℚ (Af ℚ) ((d : ℚ) / N) * ((k : Af ℚ) + l * z)
  rw [div_eq_mul_inv, map_mul, map_intCast]
  rw [ha'] at hau
  linear_combination (algebraMap ℚ (Af ℚ) (N : ℚ)⁻¹) * hau - (y : Af ℚ) * hNi

private theorem val_le (K : Type) [Field K] [NumberField K] (r : K) (v : HeightOneSpectrum (𝓞 K))
    (h : algebraMap K (Af K) r v ∈ v.adicCompletionIntegers K) : v.valuation K r ≤ 1 :=
  (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v r).symm.trans_le h

private theorem rat_int (r : ℚ) (hr : algebraMap ℚ (Af ℚ) r ∈ Ohat ℚ) : ∃ n : ℤ, r = n := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ r fun v =>
    val_le ℚ r v (memO.1 hr v)
  obtain ⟨n, hn⟩ := int_of_integers x
  exact ⟨n, hx.symm.trans hn⟩

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.ratAd :
    UpperTheory.V.Af.Nf.RatAd :=
  ⟨UpperTheory.V.Af.Nf.class_one, UpperTheory.V.Af.Nf.dense_int, UpperTheory.V.Af.Nf.rat_int⟩
