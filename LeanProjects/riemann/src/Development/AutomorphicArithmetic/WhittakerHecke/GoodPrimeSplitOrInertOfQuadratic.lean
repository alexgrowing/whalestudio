import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ComplexOrder

section

variable {E : Type} [Field E] [NumberField E]

private theorem norm_deg' (w : H.P E) : normV w = normV (w.under (𝓞 ℚ)) ^ w.asIdeal.inertiaDeg (𝓞 ℚ) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 ℚ)).isMaximal
  exact (Ideal.absNorm_pow_inertiaDeg (w.under (𝓞 ℚ)).asIdeal w.asIdeal).symm

private theorem deg_le (h2 : Module.finrank ℚ E = 2) (v : H.P ℚ)
    (T : Finset (v.asIdeal.primesOver (𝓞 E))) : ∑ q ∈ T, q.1.inertiaDeg (𝓞 ℚ) ≤ 2 := by
  have := v.isMaximal
  have : Fintype (v.asIdeal.primesOver (𝓞 E)) := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).fintype
  rw [← h2, Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 ℚ) ℚ (𝓞 E) E,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]
  refine (Finset.sum_le_sum_of_subset T.subset_univ).trans (Finset.sum_le_sum fun q _ => ?_)
  have := q.2.1
  exact Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos _ _)

private theorem norm_sq (h2 : Module.finrank ℚ E = 2) {w : H.P E}
    (h : normV w ≠ normV (w.under (𝓞 ℚ))) : normV w = normV (w.under (𝓞 ℚ)) ^ 2 := by
  have := w.isPrime
  have hs := deg_le h2 (w.under (𝓞 ℚ)) {⟨w.asIdeal, w.isPrime, ⟨rfl⟩⟩}
  rw [Finset.sum_singleton] at hs
  have h3 := w.asIdeal.inertiaDeg_pos (𝓞 ℚ)
  have h4 := norm_deg' w
  dsimp only at hs
  generalize w.asIdeal.inertiaDeg (𝓞 ℚ) = f at hs h3 h4
  interval_cases f
  · exact absurd (h4.trans (pow_one _)) h
  · exact h4

private theorem res_surj (w : H.P E) (hn : normV w = normV (w.under (𝓞 ℚ))) (x : 𝓞 E) :
    ∃ t : 𝓞 ℚ, x - algebraMap (𝓞 ℚ) (𝓞 E) t ∈ w.asIdeal := by
  have := (w.under (𝓞 ℚ)).isMaximal
  have := w.isPrime
  letI := Ideal.Quotient.field (w.under (𝓞 ℚ)).asIdeal
  have : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  let φ : (𝓞 ℚ ⧸ (w.under (𝓞 ℚ)).asIdeal) →+* (𝓞 E ⧸ w.asIdeal) :=
    Ideal.quotientMap w.asIdeal (algebraMap (𝓞 ℚ) (𝓞 E)) le_rfl
  have hb : Function.Bijective φ := (RingHom.injective φ).bijective_of_nat_card_le hn.le
  obtain ⟨c, hc⟩ := hb.2 (Ideal.Quotient.mk _ x)
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨t, Ideal.Quotient.eq.1 (hc.symm.trans ?_ )⟩
  exact Ideal.quotientMap_mk

private theorem num_den (v : H.P ℚ) {δ : ℚ} (h : v.valuation ℚ δ = 1) :
    ((δ.num : ℤ) : 𝓞 ℚ) ∉ v.asIdeal ∧ ((δ.den : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
  have hmem : ∀ a : 𝓞 ℚ, a ∈ v.asIdeal ↔ v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ a) < 1 :=
    fun a => (v.valuation_lt_one_iff_mem a).symm
  have e : v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((δ.num : ℤ) : 𝓞 ℚ)) =
      v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((δ.den : ℕ) : 𝓞 ℚ)) := by
    rw [map_intCast, map_natCast, ← Rat.mul_den_eq_num δ, map_mul, h, one_mul]
  have hiff : ((δ.num : ℤ) : 𝓞 ℚ) ∈ v.asIdeal ↔ ((δ.den : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [hmem, hmem, e]
  have hc : IsCoprime ((δ.num : ℤ) : 𝓞 ℚ) ((δ.den : ℕ) : 𝓞 ℚ) := by
    have h1 : IsCoprime δ.num (δ.den : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact δ.reduced
    simpa using h1.map (Int.castRingHom (𝓞 ℚ))
  have hnot : ¬ (((δ.num : ℤ) : 𝓞 ℚ) ∈ v.asIdeal ∧ ((δ.den : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) := by
    rintro ⟨h1, h3⟩
    obtain ⟨x, y, hxy⟩ := hc
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hxy ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left x h1) (v.asIdeal.mul_mem_left y h3)))
  exact ⟨fun h1 => hnot ⟨h1, hiff.1 h1⟩, fun h3 => hnot ⟨hiff.2 h3, h3⟩⟩

private theorem val_two {K : Type} [Field K] [NumberField K] (v : H.P K) (h : Valued.v (2 : H.Kv v) = 1) :
    v.valuation K (2 : K) = 1 := by
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (2 : K)).symm.trans ?_
  change Valued.v (algebraMap K (H.Kv v) 2) = 1
  rw [map_ofNat]
  exact h

private theorem no_ram (D : Dat ℚ E) (w : H.P E) (hG : H.Gd D.δ (w.under (𝓞 ℚ)))
    (hu : ∀ w' : H.P E, w'.under (𝓞 ℚ) = w.under (𝓞 ℚ) → w' = w)
    (hn : normV w = normV (w.under (𝓞 ℚ))) : False := by
  have hδ : (w.under (𝓞 ℚ)).valuation ℚ D.δ = 1 :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ D.δ).symm.trans hG.del
  have h2v : ((2 : ℕ) : 𝓞 ℚ) ∉ (w.under (𝓞 ℚ)).asIdeal := by
    have h := val_two _ hG.two
    have hmem : ((2 : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal ↔
        (w.under (𝓞 ℚ)).valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((2 : ℕ) : 𝓞 ℚ)) < 1 :=
      ((w.under (𝓞 ℚ)).valuation_lt_one_iff_mem _).symm
    rw [hmem, map_natCast, Nat.cast_ofNat, h]
    exact lt_irrefl _
  obtain ⟨ha, hb⟩ := num_den _ hδ
  set n : ℤ := D.δ.num with hnum
  set d : ℕ := D.δ.den with hden
  have hnd : (d : E) * algebraMap ℚ E D.δ = (n : E) := by
    have := congrArg (algebraMap ℚ E) (Rat.mul_den_eq_num D.δ)
    rw [map_mul, map_natCast, map_intCast] at this
    rw [mul_comm]
    exact this
  have hsq : ((d : E) * D.θ) ^ 2 = ((d * n : ℤ) : E) := by
    rw [mul_pow, D.sq, pow_two, mul_assoc, hnd]
    push_cast
    rfl
  have hint : IsIntegral ℤ ((d : E) * D.θ) :=
    IsIntegral.of_pow two_pos (hsq ▸ isIntegral_algebraMap (R := ℤ) (x := (d * n : ℤ)))
  obtain ⟨T, hT⟩ : ∃ T : 𝓞 E, (T : E) = (d : E) * D.θ := ⟨⟨_, hint⟩, rfl⟩
  have hT2 : T ^ 2 = algebraMap (𝓞 ℚ) (𝓞 E) (((d : ℕ) : 𝓞 ℚ) * ((n : ℤ) : 𝓞 ℚ)) := by
    refine RingOfIntegers.ext ?_
    simp only [map_pow, map_mul, map_natCast, map_intCast]
    rw [show (algebraMap (𝓞 E) E) T = (T : E) from rfl, hT, hsq]
    push_cast
    rfl
  let e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv D.σ.toRingEquiv
  have hcomm : ∀ a : 𝓞 ℚ, e (algebraMap (𝓞 ℚ) (𝓞 E) a) = algebraMap (𝓞 ℚ) (𝓞 E) a :=
    fun a => RingOfIntegers.ext (D.σ.commutes (a : ℚ))
  have h1 : w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective = w := by
    refine hu _ (HeightOneSpectrum.ext (Ideal.ext fun a => ?_))
    change e (algebraMap (𝓞 ℚ) (𝓞 E) a) ∈ w.asIdeal ↔ algebraMap (𝓞 ℚ) (𝓞 E) a ∈ w.asIdeal
    rw [hcomm]
  have he : ∀ x, x ∈ w.asIdeal → e x ∈ w.asIdeal := by
    intro x hx
    have h3 : x ∈ (w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).asIdeal := by
      rw [h1]
      exact hx
    exact h3
  have heT : e T = -T := by
    refine RingOfIntegers.ext ?_
    change D.σ (T : E) = _
    rw [hT, map_mul, map_natCast, D.conj]
    simp [hT]
  obtain ⟨t, ht⟩ := res_surj w hn T
  have ht' := he _ ht
  rw [map_sub, heT, hcomm] at ht'
  have h2T : algebraMap (𝓞 ℚ) (𝓞 E) ((2 : ℕ) : 𝓞 ℚ) * T ∈ w.asIdeal := by
    have := w.asIdeal.sub_mem ht ht'
    rw [map_natCast]
    convert this using 1
    push_cast
    ring
  have := w.isPrime
  rcases w.isPrime.mem_or_mem h2T with h | h
  · exact h2v h
  · have h5 : algebraMap (𝓞 ℚ) (𝓞 E) (((d : ℕ) : 𝓞 ℚ) * ((n : ℤ) : 𝓞 ℚ)) ∈ w.asIdeal := by
      rw [← hT2, pow_two]
      exact w.asIdeal.mul_mem_left _ h
    rcases (w.under (𝓞 ℚ)).isPrime.mem_or_mem (show _ ∈ (w.under (𝓞 ℚ)).asIdeal from h5) with h6 | h6
    · exact hb h6
    · exact ha h6

end

theorem UpperTheory.good_prime_split_or_inert_of_quadratic :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ), H.Gd D.δ v → (∃ w : H.P E, w.under (𝓞 ℚ) = v) ∧
        ∀ w : H.P E, w.under (𝓞 ℚ) = v → (normV w = normV v ∧ ∃ w' : H.P E, w' ≠ w ∧ w'.under (𝓞 ℚ) = v) ∨ normV w = normV v ^ 2 := by
  intro E _ _ D v hG
  have h2 : Module.finrank ℚ E = 2 := by simpa using Module.finrank_eq_card_basis D.b
  refine ⟨?_, fun w hw => ?_⟩
  · have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  · subst hw
    by_cases hn : normV w = normV (w.under (𝓞 ℚ))
    · refine Or.inl ⟨hn, ?_⟩
      by_contra hu
      push_neg at hu
      exact no_ram D w hG (fun w' h => by_contra fun hne => hu w' hne h) hn
    · exact Or.inr (norm_sq h2 hn)
