import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory.SplitOfSquare

private theorem valued_v_algebraMap_adicCompletion_foundation {F : Type} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (u.adicCompletion F) x) = u.valuation F x :=
  u.valuedAdicCompletion_eq_valuation' x

theorem exists_valuation_lt_one {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) (a : F) (ha : a ≠ 0)
    (h : IsSquare (algebraMap F (u.adicCompletion F) a)) : ∃ c : F, u.valuation F (1 / 4 - c ^ 2 * a) < 1 := by
  obtain ⟨s, hs⟩ := h
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply ha
    simpa using hs
  obtain ⟨π, hπ⟩ := u.valuation_exists_uniformizer F
  have hπ1 : u.valuation F π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  set h2 : u.adicCompletion F := algebraMap F (u.adicCompletion F) 2⁻¹ with hh2
  set p : u.adicCompletion F := algebraMap F (u.adicCompletion F) π with hp
  have hp0 : p ≠ 0 := (map_ne_zero _).mpr hπ0
  have hvp : Valued.v p < 1 := by rw [hp, valued_v_algebraMap_adicCompletion_foundation]; exact hπ1
  have hI := Valued.isOpen_integer (u.adicCompletion F)
  have hcont : Continuous (fun y : u.adicCompletion F => (y * s - h2) * p⁻¹) :=
    ((continuous_id.mul continuous_const).sub continuous_const).mul continuous_const
  obtain ⟨c, hc⟩ := (u.denseRange_algebraMap F).exists_mem_open (hI.preimage hcont) ⟨h2 * s⁻¹, by
    simp only [Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff]
    rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one, sub_self, zero_mul, map_zero]
    exact zero_le⟩
  refine ⟨c, ?_⟩
  simp only [Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff] at hc
  set y := algebraMap F (u.adicCompletion F) c
  set z := y * s - h2 with hz_def
  have hz : Valued.v z < 1 := by
    calc Valued.v z = Valued.v (z * p⁻¹) * Valued.v p := by
          rw [← map_mul, inv_mul_cancel_right₀ hp0]
      _ ≤ 1 * Valued.v p := by gcongr
      _ < 1 := by rw [one_mul]; exact hvp
  have hhalf : h2 + h2 = 1 := by
    rw [hh2, ← map_add, ← map_one (algebraMap F (u.adicCompletion F))]
    congr 1
    norm_num
  have hkey : algebraMap F (u.adicCompletion F) (1 / 4 - c ^ 2 * a) = -z * (1 + z) := by
    have e1 : (1 / 4 : F) = 2⁻¹ * 2⁻¹ := by norm_num
    rw [e1, map_sub, map_mul, map_mul, map_pow, hs, ← hh2]
    rw [hz_def]
    linear_combination (h2 - y * s) * hhalf
  rw [← valued_v_algebraMap_adicCompletion_foundation, hkey]
  have h1z : Valued.v (1 + z) ≤ 1 := by
    calc Valued.v (1 + z) ≤ max (Valued.v (1 : u.adicCompletion F)) (Valued.v z) :=
          Valuation.map_add _ _ _
      _ ≤ 1 := by rw [map_one]; exact max_le le_rfl hz.le
  calc Valued.v (-z * (1 + z)) = Valued.v z * Valued.v (1 + z) := by
        rw [map_mul, Valuation.map_neg]
    _ ≤ Valued.v z * 1 := by gcongr
    _ < 1 := by rw [mul_one]; exact hz

theorem valuation_complexConj_of_not_split {L : Type} [Field L] [NumberField L] [IsCMField L]
    (w : HeightOneSpectrum (𝓞 L)) (hw : ¬ IsSplitAt w) (y : L) :
    w.valuation L (IsCMField.complexConj L y) = w.valuation L y := by
  set σ : L ≃+* L := (IsCMField.complexConj L).toRingEquiv with hσ
  have hne : w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ) ≠ ⊥ := by
    intro hbot
    apply w.ne_bot
    rw [eq_bot_iff] at hbot ⊢
    intro x hx
    have hx' : (RingOfIntegers.mapRingEquiv σ).symm x ∈
        w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ) := by
      rw [Ideal.mem_comap, RingEquiv.apply_symm_apply]
      exact hx
    have h0 := hbot hx'
    rw [Ideal.mem_bot] at h0 ⊢
    simpa using h0
  obtain ⟨w', hw'⟩ : ∃ w' : HeightOneSpectrum (𝓞 L),
      w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ) :=
    ⟨⟨_, Ideal.comap_isPrime _ _, hne⟩, rfl⟩
  have hfix : ∀ x : 𝓞 (maximalRealSubfield L),
      RingOfIntegers.mapRingEquiv σ (algebraMap _ (𝓞 L) x) = algebraMap _ (𝓞 L) x := by
    intro x
    apply RingOfIntegers.ext
    rw [RingOfIntegers.mapRingEquiv_apply]
    have hx : ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) x : 𝓞 L) : L) =
        algebraMap (maximalRealSubfield L) L (x : maximalRealSubfield L) := rfl
    rw [hx]
    exact (IsCMField.complexConj L).commutes _
  have hsame : w' = w := by
    by_contra hne'
    apply hw
    refine ⟨w', hne', ?_⟩
    ext x
    simp only [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, hw', hfix]
  have key := GlobalTheory.QNorm.valuation_of_eq_comap σ w w' hw' y
  rw [hsame] at key
  exact key.symm

theorem isSplitAt_of_isSquare : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : maximalRealSubfield L) (δ : L), δ ^ 2 = a → δ ∉ maximalRealSubfield L → ∀ w : HeightOneSpectrum (𝓞 L), IsSquare (algebraMap (maximalRealSubfield L) ((w.under (𝓞 (maximalRealSubfield L))).adicCompletion (maximalRealSubfield L)) a) → IsSplitAt w := by
  intro L _ _ _ a δ hδ hδL w hsq
  by_contra hw
  set u := w.under (𝓞 (maximalRealSubfield L)) with hu
  have ha : a ≠ 0 := by
    rintro rfl
    apply hδL
    have h0 : δ = 0 := by simpa using hδ
    rw [h0]
    exact zero_mem _
  obtain ⟨c, hc⟩ := exists_valuation_lt_one u a ha hsq
  have hconj : IsCMField.complexConj L δ = -δ := by
    have h1 : (IsCMField.complexConj L δ) ^ 2 = δ ^ 2 := by
      rw [← map_pow, hδ, IsCMField.complexConj_apply_eq_self]
    have h2 : IsCMField.complexConj L δ ≠ δ := fun h =>
      hδL ((IsCMField.complexConj_eq_self_iff L δ).mp h)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact absurd h h2
    · exact h
  set x : L := 2⁻¹ + (c : L) * δ with hx
  have hcc : IsCMField.complexConj L (c : L) = c := IsCMField.complexConj_apply_eq_self L c
  have hx' : IsCMField.complexConj L x = 2⁻¹ - (c : L) * δ := by
    rw [hx, map_add, map_mul, hcc, hconj, map_inv₀, map_ofNat]
    ring
  have hsum : x + IsCMField.complexConj L x = 1 := by
    rw [hx', hx]
    ring
  have hprod : x * IsCMField.complexConj L x =
      algebraMap (maximalRealSubfield L) L (1 / 4 - c ^ 2 * a) := by
    rw [hx', hx]
    simp only [map_sub, map_mul, map_pow, map_div₀, map_one, map_ofNat]
    change _ = 1 / 4 - (c : L) ^ 2 * (a : L)
    linear_combination (-(c : L) ^ 2) * hδ
  have : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  have hlt : w.valuation L (x * IsCMField.complexConj L x) < 1 := by
    rw [hprod, ← HeightOneSpectrum.valuation_liesOver L u w]
    exact pow_lt_one₀ zero_le hc (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal u.ne_bot)
  have heq := valuation_complexConj_of_not_split w hw x
  rw [map_mul, heq] at hlt
  have hx1 : w.valuation L x < 1 := by
    by_contra hge
    push Not at hge
    exact absurd hlt (not_lt.mpr (one_le_mul hge hge))
  have hadd := Valuation.map_add (w.valuation L) x (IsCMField.complexConj L x)
  rw [hsum, map_one, heq, max_self] at hadd
  exact absurd (lt_of_le_of_lt hadd hx1) (lt_irrefl 1)

end GlobalTheory.SplitOfSquare
