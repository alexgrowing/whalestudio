import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private theorem exists_pow_mul_isIntegral_of_valuation_le_one_away {F : Type} [Field F] [NumberField F] (c : 𝓞 F) (x : F)
    (h : ∀ P : HeightOneSpectrum (𝓞 F), c ∉ P.asIdeal → HeightOneSpectrum.valuation F P x ≤ 1) :
    ∃ n : ℕ, ∃ a : 𝓞 F, (c : F) ^ n * x = a := by
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (𝓞 F) x
  have hpq' : (p : F) / q = x := hpq
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hq0' : (q : F) ≠ 0 := by exact_mod_cast hq0
  let T : Ideal (𝓞 F) := (LinearMap.range (Algebra.linearMap (𝓞 F) F)).comap
    (LinearMap.toSpanSingleton (𝓞 F) F x)
  have memT : ∀ y : 𝓞 F, y ∈ T ↔ ∃ a : 𝓞 F, (y : F) * x = a := by
    intro y
    simp only [T, Submodule.mem_comap, LinearMap.mem_range, LinearMap.toSpanSingleton_apply,
      Algebra.linearMap_apply, Algebra.smul_def]
    constructor <;> rintro ⟨a, ha⟩ <;> exact ⟨a, ha.symm⟩
  have hqT : q ∈ T := (memT q).2 ⟨p, by rw [← hpq']; field_simp⟩
  have hrad : c ∈ T.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hTP, hP⟩
    by_contra hc
    have hPne : P ≠ ⊥ := by
      intro h0
      have := hTP hqT
      rw [h0] at this
      exact hq0 (Ideal.mem_bot.1 this)
    let v : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hPne⟩
    have hv := h v hc
    have hspan : Ideal.span {q} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hq0
    have hPunit : ¬ IsUnit P := by
      rw [Ideal.isUnit_iff]
      exact hP.ne_top
    obtain ⟨n, J, hPJ, hJ⟩ := WfDvdMonoid.max_power_factor' hspan hPunit
    rw [Ideal.dvd_iff_le] at hPJ
    obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hPJ
    have hvq : v.intValuation q ≤ WithZero.exp (-(n : ℤ)) :=
      (v.intValuation_le_pow_iff_dvd q n).2 ⟨J, hJ⟩
    have hq' : v.intValuation q ≠ 0 := by
      rw [← v.valuation_of_algebraMap (K := F)]
      simpa using hq0'
    have hvp : v.intValuation p ≤ WithZero.exp (-(n : ℤ)) := by
      have hx : HeightOneSpectrum.valuation F v x = v.intValuation p / v.intValuation q := by
        rw [← hpq', map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap]
      rw [hx, div_le_one₀ (zero_lt_iff.2 hq')] at hv
      exact hv.trans hvq
    have hpn := (v.intValuation_le_pow_iff_dvd p n).1 hvp
    rw [Ideal.dvd_iff_le] at hpn
    have hps : p * s ∈ Ideal.span {q} := by
      rw [hJ]
      exact Ideal.mul_mem_mul (hpn (Ideal.mem_span_singleton_self p)) hsJ
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hps
    have hd' : (d : F) * q = p * s := by exact_mod_cast hd
    refine hsP (hTP ((memT s).2 ⟨d, ?_⟩))
    rw [← hpq']
    field_simp
    linear_combination -hd'
  obtain ⟨n, hn⟩ := hrad
  obtain ⟨a, ha⟩ := (memT _).1 hn
  exact ⟨n, a, by push_cast at ha; exact ha⟩

theorem UpperTheory.V.ZK.Cl.cRes :
    UpperTheory.V.ZK.Cl.CRes := by
  intro L F _ _ _ _ _ k _ r
  have uniq : ∀ (x : F) (u u' : k), ResF r x u → ResF r x u' → u = u' := by
    rintro x u u' ⟨a, b, hb, hx, hu⟩ ⟨a', b', hb', hx', hu'⟩
    have h1 : a * b' = a' * b := by
      have : (a : F) * b' = a' * b := by
        rw [← hx, ← hx']
        ring
      exact_mod_cast this
    have h2 := congrArg r h1
    rw [map_mul, map_mul, hu, hu'] at h2
    have h3 : (u - u') * (r b * r b') = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h (mul_ne_zero hb hb')
  have base : ∀ a : 𝓞 F, ResF r (a : F) (r a) := fun a => ⟨a, 1, by simp, by simp, by simp⟩
  have arith : ∀ (x y : F) (u w : k), ResF r x u → ResF r y w →
      ResF r (x + y) (u + w) ∧ ResF r (x * y) (u * w) := by
    rintro x y u w ⟨a, b, hb, hx, hu⟩ ⟨a', b', hb', hy, hw⟩
    refine ⟨⟨a * b' + a' * b, b * b', by simpa using mul_ne_zero hb hb', ?_, ?_⟩,
      ⟨a * a', b * b', by simpa using mul_ne_zero hb hb', ?_, ?_⟩⟩
    · have e : ((a * b' + a' * b : 𝓞 F) : F) = (a : F) * b' + a' * b := by push_cast; rfl
      have e' : ((b * b' : 𝓞 F) : F) = (b : F) * b' := by push_cast; rfl
      rw [e, e', ← hx, ← hy]
      ring
    · simp only [map_add, map_mul, hu, hw]
      ring
    · have e : ((a * a' : 𝓞 F) : F) = (a : F) * a' := by push_cast; rfl
      have e' : ((b * b' : 𝓞 F) : F) = (b : F) * b' := by push_cast; rfl
      rw [e, e', ← hx, ← hy]
      ring
    · simp only [map_mul, hu, hw]
      ring
  have integ : ∀ b : 𝓞 L, r (algebraMap (𝓞 L) (𝓞 F) b) ≠ 0 → ∀ x : F,
      (∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal →
        HeightOneSpectrum.valuation F P x ≤ 1) →
      (∃ n, ∃ a : 𝓞 F, algebraMap (𝓞 L) F b ^ n * x = a) ∧ ∃ u, ResF r x u := by
    intro b hb x hx
    obtain ⟨n, a, ha⟩ := exists_pow_mul_isIntegral_of_valuation_le_one_away _ x hx
    have hcast : algebraMap (𝓞 L) F b = ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 F) F]
    refine ⟨⟨n, a, by rw [hcast]; exact ha⟩, ⟨r a / r (algebraMap (𝓞 L) (𝓞 F) b ^ n), a,
      algebraMap (𝓞 L) (𝓞 F) b ^ n, by rw [map_pow]; exact pow_ne_zero _ hb, ?_, ?_⟩⟩
    · have e : ((algebraMap (𝓞 L) (𝓞 F) b ^ n : 𝓞 F) : F)
          = ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) ^ n := by push_cast; rfl
      rw [e, mul_comm]
      exact ha
    · rw [div_mul_cancel₀]
      rw [map_pow]
      exact pow_ne_zero _ hb
  refine ⟨uniq, base, arith, fun b hb => ⟨integ b hb, ?_⟩⟩
  intro α hα
  have hval : ∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal →
      HeightOneSpectrum.valuation F P (α : F) = 1 := by
    intro P hP
    have h0 := hα P hP
    unfold ordP at h0
    have hne : HeightOneSpectrum.valuation F P (α : F) ≠ 0 := by simp
    rw [← WithZero.exp_log hne]
    have : (HeightOneSpectrum.valuation F P (α : F)).log = 0 := by linarith
    rw [this]
    rfl
  obtain ⟨-, u, hu⟩ := integ b hb (α : F) (fun P hP => (hval P hP).le)
  obtain ⟨-, u', hu'⟩ := integ b hb ((α⁻¹ : Fˣ) : F) (fun P hP => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hval P hP, inv_one])
  have hmul := (arith _ _ _ _ hu hu').2
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one] at hmul
  have h1 : ResF r (1 : F) 1 := by simpa using base 1
  have huu : u * u' = 1 := uniq _ _ _ hmul h1
  exact ⟨⟨u, u', huu, by rw [mul_comm]; exact huu⟩, hu⟩
