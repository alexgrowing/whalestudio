import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSeparableCompositum

open NumberField IsDedekindDomain

namespace GlobalTheory.CommonValuation

theorem exists_eq_pow {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
    (P : HeightOneSpectrum R) (u : Valuation F (WithZero (Multiplicative ℤ)))
    (h1 : ∀ r : R, u (algebraMap R F r) ≤ 1) (h2 : ∀ r : R, u (algebraMap R F r) < 1 ↔ r ∈ P.asIdeal) :
    ∃ e : ℕ, 0 < e ∧ ∀ x : F, u x = P.valuation F x ^ e := by
  have hu : ∀ r : R, r ∉ P.asIdeal → u (algebraMap R F r) = 1 := fun r hr =>
    le_antisymm (h1 r) (not_lt.1 fun h => hr ((h2 r).1 h))
  have hone : ∀ x : F, P.valuation F x = 1 → u x = 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x hx.le
    have hn : n ∉ P.asIdeal := by
      rw [← P.valuation_eq_one_iff_notMem (K := F), ← h, map_mul, hx, one_mul]
      exact (P.valuation_eq_one_iff_notMem (K := F)).2 d.2
    have := congrArg u h
    rwa [map_mul, hu _ d.2, hu _ hn, mul_one] at this
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  have hπ' : P.valuation F (algebraMap R F π) = WithZero.exp (-1) := (P.valuation_of_algebraMap π).trans hπ
  have l1 : (WithZero.exp (-1) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hπ0 : algebraMap R F π ≠ 0 := fun h => by
    rw [h, map_zero] at hπ'
    exact WithZero.exp_ne_zero hπ'.symm
  have hlt : u (algebraMap R F π) < 1 := (h2 π).2 ((P.valuation_lt_one_iff_mem (K := F) π).1 (hπ' ▸ l1))
  have hu0 : u (algebraMap R F π) ≠ 0 := by simpa using hπ0
  obtain ⟨e, he⟩ : ∃ e : ℕ, WithZero.log (u (algebraMap R F π)) = -(e : ℤ) ∧ 0 < e := by
    rw [← WithZero.exp_log hu0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    exact ⟨(-WithZero.log (u (algebraMap R F π))).toNat, by omega, by omega⟩
  refine ⟨e, he.2, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp [he.2.ne']
  have h0 : P.valuation F x ≠ 0 := by simpa using hx
  have h3 := hone (x * algebraMap R F π ^ WithZero.log (P.valuation F x)) (by
    rw [map_mul, map_zpow₀, hπ', ← WithZero.exp_zsmul]
    nth_rewrite 1 [← WithZero.exp_log h0]
    rw [← WithZero.exp_add]; simp)
  rw [map_mul, map_zpow₀, ← WithZero.exp_log hu0, he.1, ← WithZero.exp_zsmul,
    mul_eq_one_iff_eq_inv₀ WithZero.exp_ne_zero, ← WithZero.exp_neg] at h3
  rw [h3]
  nth_rewrite 2 [← WithZero.exp_log h0]
  rw [← WithZero.exp_nsmul]
  congr 1
  simp [mul_comm]

theorem exists_dvr (V K L : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra W L)
      (_ : IsFractionRing W L) (f : V →+* W), (∀ z : V, algebraMap W L (f z) = algebraMap K L (algebraMap V K z)) ∧
      ∀ z : V, f z ∈ IsLocalRing.maximalIdeal W ↔ z ∈ IsLocalRing.maximalIdeal V := by
  let _ : Algebra V L := ((algebraMap K L).comp (algebraMap V K)).toAlgebra
  have : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsDedekindDomain (integralClosure V L) := integralClosure.isDedekindDomain V K L
  have : IsFractionRing (integralClosure V L) L := integralClosure.isFractionRing_of_finite_extension K L
  have hinj : Function.Injective (algebraMap V (integralClosure V L)) := fun a b h =>
    IsFractionRing.injective V K ((algebraMap K L).injective (congrArg Subtype.val h))
  obtain ⟨M, -, hM, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := integralClosure V L)
    (IsLocalRing.maximalIdeal V) ⊥ (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  have h0 : M ≠ ⊥ := by
    rintro rfl
    rw [Ideal.comap_bot_of_injective _ hinj] at hc
    exact IsDiscreteValuationRing.not_a_field V hc.symm
  let P : HeightOneSpectrum (integralClosure V L) := ⟨M, hM, h0⟩
  refine ⟨(P.valuation L).valuationSubring, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (algebraMap V L).codRestrict (P.valuation L).valuationSubring.toSubring
      (fun z => P.valuation_le_one (K := L) (algebraMap V _ z)), fun _ => rfl, fun z => ?_⟩
  rw [Valuation.mem_maximalIdeal_iff, ← hc]
  exact P.valuation_lt_one_iff_mem (K := L) (algebraMap V _ z)

theorem le_one_of_ringOfIntegers {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (u : Valuation F Γ)
    (r : 𝓞 F) : u (algebraMap (𝓞 F) F r) ≤ 1 :=
  (Valuation.integer.integers u).isIntegral_iff_v_le_one.1 r.isIntegral_coe.tower_top

theorem exists_centre {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (u : Valuation F Γ) :
    ∃ Q : Ideal (𝓞 F), Q.IsPrime ∧ ∀ r, r ∈ Q ↔ u (algebraMap (𝓞 F) F r) < 1 := by
  refine ⟨{ carrier := {r | u (algebraMap (𝓞 F) F r) < 1}
            add_mem' := fun {a b} ha hb => ?_
            zero_mem' := by simp
            smul_mem' := fun c r hr => ?_ }, ⟨?_, fun {a b} h => ?_⟩, fun _ => Iff.rfl⟩
  · change u _ < 1
    rw [map_add]
    exact u.map_add_lt ha hb
  · change u _ < 1
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_of_le_one_left' (le_one_of_ringOfIntegers u c)).trans_lt hr
  · rw [Ideal.ne_top_iff_one]
    change ¬ u _ < 1
    simp
  · by_contra! hn
    have ha : u (algebraMap _ F a) = 1 := le_antisymm (le_one_of_ringOfIntegers u a) (not_lt.1 hn.1)
    have hb : u (algebraMap _ F b) = 1 := le_antisymm (le_one_of_ringOfIntegers u b) (not_lt.1 hn.2)
    change u _ < 1 at h
    rw [map_mul, map_mul, ha, hb, mul_one] at h
    exact lt_irrefl _ h

theorem exists_common_valuation : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (em : k →+* K) (e : ℕ), (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → 0 < e → (∀ z : k, (IsDiscreteValuationRing.maximalIdeal V).valuation K (em z) = 𝔭.valuation k z ^ e) → ∃ (W L : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Field L) (_ : Algebra W L) (_ : IsFractionRing W L) (f : V →+* W) (g : K →+* L) (em' : k' →+* L) (e' d : ℕ), (∀ z : V, algebraMap W L (f z) = g (algebraMap V K z)) ∧ em'.comp i = g.comp em ∧ 0 < e' ∧ e' * ε = d * e ∧ (∀ z : k', (IsDiscreteValuationRing.maximalIdeal W).valuation L (em' z) = 𝔓.valuation k' z ^ e') ∧ ∀ y : K, (IsDiscreteValuationRing.maximalIdeal W).valuation L (g y) = (IsDiscreteValuationRing.maximalIdeal V).valuation K y ^ d := by
  intro k k' _ _ _ _ i 𝔭 𝔓 ε V K _ _ _ _ _ _ em e hε he hem
  let _ : Algebra k k' := i.toAlgebra
  let N := IntermediateField.normalClosure k k' (AlgebraicClosure k')
  have : NumberField N := NumberField.of_module_finite k N
  obtain ⟨L, _, _, j, _, _, hj⟩ := exists_finite_separable_compositum k K N em
  have hj' : ∀ z, j (algebraMap k N z) = algebraMap K L (em z) := fun z => DFunLike.congr_fun hj z
  obtain ⟨W, _, _, _, _, _, f, hf, hfm⟩ := exists_dvr V K L
  let w := (IsDiscreteValuationRing.maximalIdeal W).valuation L
  obtain ⟨d, hd, hdv⟩ := exists_eq_pow (IsDiscreteValuationRing.maximalIdeal V) (w.comap (algebraMap K L))
    (fun r => by
      rw [Valuation.comap_apply, ← hf]
      exact (IsDiscreteValuationRing.maximalIdeal W).valuation_le_one (f r))
    (fun r => by
      rw [Valuation.comap_apply, ← hf]
      exact ((IsDiscreteValuationRing.maximalIdeal W).valuation_lt_one_iff_mem (K := L) (f r)).trans (hfm r))
  have hε0 : ε ≠ 0 := by
    rintro rfl
    simpa using hε 0
  obtain ⟨Q, hQ, hQm⟩ := exists_centre (w.comap j)
  obtain ⟨Q', hQ', hQo⟩ := (inferInstance : Nonempty (𝔓.asIdeal.primesOver (𝓞 N)))
  have hpow : ∀ {x : WithZero (Multiplicative ℤ)} {n : ℕ}, n ≠ 0 → (x ^ n < 1 ↔ x < 1) := fun hn =>
    pow_lt_one_iff_of_nonneg zero_le hn
  have hund : Q.under (𝓞 k) = Q'.under (𝓞 k) := by
    ext r
    rw [← Ideal.under_under (B := 𝓞 k') Q', ← hQo.over]
    change algebraMap _ _ r ∈ Q ↔ algebraMap _ _ r ∈ 𝔓.asIdeal
    rw [hQm, ← 𝔓.valuation_lt_one_iff_mem (K := k')]
    change w (j (algebraMap k N r)) < 1 ↔ 𝔓.valuation k' (i r) < 1
    rw [hj', hε, hpow hε0]
    change w.comap (algebraMap K L) _ < 1 ↔ _
    rw [hdv, hem, hpow hd.ne', hpow he.ne']
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 k) (𝓞 N) (N ≃ₐ[k] N) Q' Q hund.symm
  let em' : k' →+* L := j.comp (σ.toRingEquiv.toRingHom.comp (algebraMap k' N))
  have hc : ∀ z, em' (i z) = algebraMap K L (em z) := fun z => by
    rw [← hj', ← σ.commutes z, IsScalarTower.algebraMap_apply k k' N]
    rfl
  obtain ⟨e', he', hv⟩ := exists_eq_pow 𝔓 (w.comap em') (le_one_of_ringOfIntegers _) (fun r => by
    rw [hQo.over]
    change _ ↔ algebraMap _ _ r ∈ Q'
    rw [← Ideal.smul_mem_pointwise_smul_iff (a := σ), ← hσ, hQm]
    rfl)
  refine ⟨W, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, f,
    algebraMap K L, em', e', d, hf, RingHom.ext hc, he', ?_, hv, hdv⟩
  obtain ⟨π, hπ⟩ := 𝔭.valuation_exists_uniformizer k
  have h1 := hv (i π)
  rw [Valuation.comap_apply, hc, hε] at h1
  have h2 := hdv (em π)
  rw [Valuation.comap_apply, h1, hem, hπ, ← pow_mul, ← pow_mul, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul,
    WithZero.exp_inj] at h2
  simp only [smul_neg, nsmul_eq_mul, mul_one, neg_inj, Nat.cast_inj] at h2
  rw [mul_comm, h2, mul_comm]

end GlobalTheory.CommonValuation
