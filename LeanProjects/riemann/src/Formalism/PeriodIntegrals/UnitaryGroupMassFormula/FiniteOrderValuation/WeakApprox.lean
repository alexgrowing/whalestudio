import Mathlib

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace PI.FinOrdValD.WA

variable {L : Type*} [Field L] [NumberField L]

lemma val_alg (v : HeightOneSpectrum (𝓞 L)) (a : L) :
    Valued.v (algebraMap L (v.adicCompletion L) a) = v.valuation L a := by
  first
  | exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
  | exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation v a
  | simp

lemma exists_pow_lt {δ : ℤᵐ⁰} (hδ : δ ≠ 0) : ∃ n : ℕ, exp (-(n : ℤ)) < δ := by
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, exp k = δ := ⟨log δ, exp_log hδ⟩
  refine ⟨k.natAbs + 1, ?_⟩
  rw [exp_lt_exp]
  omega

lemma val_nat_le_one (v : HeightOneSpectrum (𝓞 L)) (m : ℕ) : v.valuation L (m : L) ≤ 1 := by
  have h := v.valuation_le_one (K := L) (m : 𝓞 L)
  simpa using h

private lemma pow_le_exp_neg_of_lt_one (x : ℤᵐ⁰) (hx : x < 1) (n : ℕ) : x ^ n ≤ exp (-(n : ℤ)) := by
  rcases eq_or_ne x 0 with rfl | h0
  · rcases n with _ | n
    · simp
    · simp [zero_pow (Nat.succ_ne_zero n)]
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, exp k = x := ⟨log x, exp_log h0⟩
    have hk : k ≤ -1 := by
      have : k < 0 := by rwa [← exp_zero, exp_lt_exp] at hx
      omega
    rw [← exp_nsmul, exp_le_exp, nsmul_eq_mul]
    nlinarith [(Int.natCast_nonneg n : (0 : ℤ) ≤ n)]

lemma exists_nat_small (T : Finset (HeightOneSpectrum (𝓞 L))) (δ : HeightOneSpectrum (𝓞 L) → ℤᵐ⁰)
    (hδ : ∀ v ∈ T, δ v ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ v ∈ T, v.valuation L (N : L) < δ v := by
  classical
  have hpos : ∀ w : HeightOneSpectrum (𝓞 L), 0 < Ideal.absNorm w.asIdeal := fun w =>
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot)
  set M : ℕ := ∏ w ∈ T, Ideal.absNorm w.asIdeal with hM
  have hM0 : 0 < M := Finset.prod_pos fun w _ => hpos w
  have hMv : ∀ w ∈ T, w.valuation L (M : L) < 1 := by
    intro w hw
    have hmem : ((M : ℕ) : 𝓞 L) ∈ w.asIdeal := by
      obtain ⟨c, hc⟩ : Ideal.absNorm w.asIdeal ∣ M := Finset.dvd_prod_of_mem _ hw
      rw [hc, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    have := (w.valuation_lt_one_iff_mem (K := L) _).mpr hmem
    simpa using this
  let n : HeightOneSpectrum (𝓞 L) → ℕ := fun w =>
    if h : δ w ≠ 0 then Classical.choose (exists_pow_lt h) else 0
  refine ⟨M ^ (∑ w ∈ T, n w), pow_pos hM0 _, fun w hw => ?_⟩
  have hn : exp (-((n w : ℕ) : ℤ)) < δ w := by
    simp only [n, dif_pos (hδ w hw)]
    exact Classical.choose_spec (exists_pow_lt (hδ w hw))
  have hle : n w ≤ ∑ u ∈ T, n u := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw
  calc w.valuation L ((M ^ (∑ u ∈ T, n u) : ℕ) : L)
        = (w.valuation L (M : L)) ^ (∑ u ∈ T, n u) := by rw [Nat.cast_pow, map_pow]
    _ ≤ exp (-((∑ u ∈ T, n u : ℕ) : ℤ)) := pow_le_exp_neg_of_lt_one _ (hMv w hw) _
    _ ≤ exp (-((n w : ℕ) : ℤ)) := by rw [exp_le_exp]; omega
    _ < δ w := hn

lemma exists_near (v : HeightOneSpectrum (𝓞 L)) (x : v.adicCompletion L) {δ : ℤᵐ⁰} (hδ : δ ≠ 0) :
    ∃ b : L, Valued.v (algebraMap L (v.adicCompletion L) b - x) < δ := by
  have hd : DenseRange (algebraMap L (v.adicCompletion L)) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap L v
  have hs : {y : v.adicCompletion L | Valued.v (y - x) < δ} ∈ nhds x := by
    obtain ⟨N, hN, hNv⟩ := exists_nat_small {v} (fun _ => δ) (fun _ _ => hδ)
    have hNv' := hNv v (Finset.mem_singleton_self v)
    set z : v.adicCompletion L := algebraMap L (v.adicCompletion L) (N : L) with hz
    have hz0 : z ≠ 0 := by
      rw [hz, Ne, map_eq_zero_iff _ (algebraMap L (v.adicCompletion L)).injective]
      exact_mod_cast hN.ne'
    have hvz : Valued.v z < δ := by rw [hz, val_alg]; exact hNv'
    rw [Valued.mem_nhds]
    refine ⟨Units.mk0 (Valued.v.restrict z) ((Valuation.ne_zero_iff _).mpr hz0), fun y hy => ?_⟩
    have hy' : Valued.v.restrict (y - x) < Valued.v.restrict z := hy
    rw [Valuation.restrict_lt_iff] at hy'
    exact lt_trans hy' hvz
  obtain ⟨_, hy, ⟨b, rfl⟩⟩ := mem_closure_iff_nhds.mp (hd x) _ hs
  exact ⟨b, hy⟩

theorem weakApprox (T : Finset (HeightOneSpectrum (𝓞 L)))
    (x : (v : HeightOneSpectrum (𝓞 L)) → v.adicCompletion L)
    (γ : HeightOneSpectrum (𝓞 L) → ℤᵐ⁰) (hγ : ∀ v ∈ T, γ v ≠ 0) :
    ∃ a : L, a ≠ 0 ∧ (∀ v ∈ T, Valued.v (algebraMap L (v.adicCompletion L) a - x v) < γ v) ∧
      ∀ σ : L →+* ℝ, 0 < σ a := by
  classical
  have hnear : ∀ w : T, ∃ b : L, Valued.v (algebraMap L (w.1.adicCompletion L) b - x w.1) < γ w.1 :=
    fun w => exists_near w.1 (x w.1) (hγ w.1 w.2)
  choose b hb using hnear
  obtain ⟨⟨d, hd⟩, hdint⟩ := IsLocalization.exist_integer_multiples (M := nonZeroDivisors (𝓞 L))
    (S := L) (s := (Finset.univ : Finset T)) (f := b)
  have hr : ∀ w : T, ∃ r : 𝓞 L, algebraMap (𝓞 L) L r = algebraMap (𝓞 L) L d * b w := by
    intro w
    obtain ⟨r, hr⟩ := hdint w (Finset.mem_univ _)
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  choose r hr using hr
  set dL : L := algebraMap (𝓞 L) L d with hdL
  have hdL0 : dL ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hvd : ∀ w : HeightOneSpectrum (𝓞 L), w.valuation L dL ≠ 0 := fun w =>
    (Valuation.ne_zero_iff _).mpr hdL0
  let e : HeightOneSpectrum (𝓞 L) → ℕ := fun w =>
    if h : w ∈ T then Classical.choose (exists_pow_lt (mul_ne_zero (hγ w h) (hvd w))) else 0
  have he : ∀ w (h : w ∈ T), exp (-((e w : ℕ) : ℤ)) < γ w * w.valuation L dL := by
    intro w h
    simp only [e, dif_pos h]
    exact Classical.choose_spec (exists_pow_lt (mul_ne_zero (hγ w h) (hvd w)))
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun w : HeightOneSpectrum (𝓞 L) => w.asIdeal) e
    (fun w _ => Ideal.prime_of_isPrime w.ne_bot w.isPrime)
    (fun w _ u _ hne h => hne (HeightOneSpectrum.ext h)) r
  set a0 : L := algebraMap (𝓞 L) L y / dL with ha0
  have hclose : ∀ w ∈ T, Valued.v (algebraMap L (w.adicCompletion L) a0 - x w) < γ w := by
    intro w hw
    have hmem := hy w hw
    have hval : w.valuation L (algebraMap (𝓞 L) L (y - r ⟨w, hw⟩)) ≤ exp (-((e w : ℕ) : ℤ)) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      first
      | exact (w.intValuation_le_pow_iff_mem _ _).mpr hmem
      | exact (w.intValuation_le_pow_iff_dvd _ _).mpr (Ideal.dvd_span_singleton.mpr hmem)
    have hnum : algebraMap (𝓞 L) L (y - r ⟨w, hw⟩) = (a0 - b ⟨w, hw⟩) * dL := by
      rw [map_sub, hr, ha0, sub_mul, div_mul_cancel₀ _ hdL0, mul_comm dL]
    rw [hnum, Valuation.map_mul] at hval
    have h1 : w.valuation L (a0 - b ⟨w, hw⟩) < γ w := by
      by_contra hle
      push_neg at hle
      exact absurd (lt_of_le_of_lt hval (he w hw)) (not_lt.mpr (mul_le_mul_of_nonneg_right hle zero_le'))
    have hsplit : algebraMap L (w.adicCompletion L) a0 - x w =
        algebraMap L (w.adicCompletion L) (a0 - b ⟨w, hw⟩) +
          (algebraMap L (w.adicCompletion L) (b ⟨w, hw⟩) - x w) := by
      rw [map_sub]; ring
    rw [hsplit]
    exact Valuation.map_add_lt _ (by rw [val_alg]; exact h1) (hb ⟨w, hw⟩)
  obtain ⟨N, hN, hNs⟩ := exists_nat_small T γ hγ
  haveI : Finite (L →+* ℝ) := Finite.of_injective (fun σ : L →+* ℝ => Complex.ofRealHom.comp σ)
    (fun σ τ h => RingHom.ext fun z => Complex.ofReal_injective (RingHom.congr_fun h z))
  obtain ⟨B, hB⟩ := (Set.finite_range (fun σ : L →+* ℝ => |σ a0|)).bddAbove
  obtain ⟨t, ht⟩ := exists_nat_gt B
  have good : ∀ s : ℕ, B < s → (∀ w ∈ T, Valued.v (algebraMap L (w.adicCompletion L)
      (a0 + (N : L) * (s : L)) - x w) < γ w) ∧ ∀ σ : L →+* ℝ, 0 < σ (a0 + (N : L) * (s : L)) := by
    intro s hs
    refine ⟨fun w hw => ?_, fun σ => ?_⟩
    · have hsplit : algebraMap L (w.adicCompletion L) (a0 + (N : L) * (s : L)) - x w =
          (algebraMap L (w.adicCompletion L) a0 - x w) +
            algebraMap L (w.adicCompletion L) ((N : L) * (s : L)) := by
        rw [map_add]; ring
      rw [hsplit]
      refine Valuation.map_add_lt _ (hclose w hw) ?_
      rw [val_alg, Valuation.map_mul]
      calc w.valuation L (N : L) * w.valuation L (s : L) ≤ w.valuation L (N : L) * 1 :=
            mul_le_mul_of_nonneg_left (val_nat_le_one w s) zero_le'
        _ = w.valuation L (N : L) := mul_one _
        _ < γ w := hNs w hw
    · have h1 : |σ a0| ≤ B := hB ⟨σ, rfl⟩
      have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
      have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      rw [map_add, map_mul, map_natCast, map_natCast]
      nlinarith [neg_abs_le (σ a0), mul_nonneg (sub_nonneg.mpr hN1) hs0]
  by_cases h0 : a0 + (N : L) * (t : L) = 0
  · have ht1 : B < ((t + 1 : ℕ) : ℝ) := by push_cast; linarith
    refine ⟨a0 + (N : L) * ((t + 1 : ℕ) : L), ?_, (good (t + 1) ht1).1, (good (t + 1) ht1).2⟩
    intro h1
    have hN0 : (N : L) = 0 := by push_cast at h1; linear_combination h1 - h0
    exact hN.ne' (by exact_mod_cast hN0)
  · exact ⟨a0 + (N : L) * (t : L), h0, (good t ht).1, (good t ht).2⟩

theorem weakApprox_units (T : Finset (HeightOneSpectrum (𝓞 L)))
    (x : (v : HeightOneSpectrum (𝓞 L)) → (v.adicCompletion L)ˣ) (e : HeightOneSpectrum (𝓞 L) → ℤ) :
    ∃ a : Lˣ, (∀ v ∈ T, Valued.v (algebraMap L (v.adicCompletion L) (a : L) * ((x v)⁻¹ : (v.adicCompletion L)ˣ) - 1) <
        exp (-e v)) ∧ ∀ σ : L →+* ℝ, 0 < σ (a : L) := by
  classical
  have hx0 : ∀ w : HeightOneSpectrum (𝓞 L), Valued.v (x w : w.adicCompletion L) ≠ 0 := fun w =>
    (Valuation.ne_zero_iff _).mpr (x w).ne_zero
  obtain ⟨a, ha0, hT, hpos⟩ := weakApprox T (fun w => (x w : w.adicCompletion L))
    (fun w => exp (-e w) * Valued.v (x w : w.adicCompletion L))
    (fun w _ => mul_ne_zero (exp_ne_zero) (hx0 w))
  refine ⟨Units.mk0 a ha0, fun w hw => ?_, fun σ => hpos σ⟩
  have h := hT w hw
  have key : algebraMap L (w.adicCompletion L) a * (((x w)⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1 =
      (algebraMap L (w.adicCompletion L) a - x w) * (((x w)⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L) := by
    rw [sub_mul, Units.mul_inv]
  have hinv : Valued.v (((x w)⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L) *
      Valued.v (x w : w.adicCompletion L) = 1 := by
    rw [← Valuation.map_mul, Units.inv_mul, Valuation.map_one]
  rw [Units.val_mk0, key, Valuation.map_mul]
  by_contra hle
  push_neg at hle
  have h2 := mul_le_mul_of_nonneg_right hle (zero_le' : 0 ≤ Valued.v (x w : w.adicCompletion L))
  rw [mul_assoc, hinv, mul_one] at h2
  exact absurd h (not_lt.mpr h2)

end PI.FinOrdValD.WA
