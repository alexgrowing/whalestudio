import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped nonZeroDivisors

namespace GlobalTheory.NumeratorIdeal

section general
variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem count_span_int (v : HeightOneSpectrum R) {a : R} (ha : a ≠ 0) :
    v.valuation K (algebraMap R K a) =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a))) := by
  classical
  have hJ : (Ideal.span {a} : Ideal R) ≠ 0 := by simpa using ha
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v hJ,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg v ha]

theorem valuation_eq_count (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    v.valuation K x =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have ha' : algebraMap R K a ≠ 0 := by simpa using ha0
  have hb' : algebraMap R K b ≠ 0 := by simpa using hb0
  rw [map_div₀, count_span_int K v ha0, count_span_int K v hb0, div_eq_mul_inv (algebraMap R K a),
    ← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K v
      (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using ha0)
      (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hb0),
    ← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, ← WithZero.exp_sub]
  congr 1
  ring

theorem le_one_of_count {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, 0 ≤ FractionalIdeal.count K v I) : I ≤ 1 := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
  refine finprod_induction (fun J : FractionalIdeal R⁰ K => J ≤ 1) le_rfl
    (fun a b ha hb => mul_le_one' ha hb) fun v => ?_
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h v)
  show _ ≤ _
  rw [hn, zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
  exact FractionalIdeal.coeIdeal_le_one

theorem le_of_count {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v J ≤ FractionalIdeal.count K v I) :
    I ≤ J := by
  have h1 : I * J⁻¹ ≤ 1 := le_one_of_count K (mul_ne_zero hI (inv_ne_zero hJ)) fun v => by
    rw [FractionalIdeal.count_mul K v hI (inv_ne_zero hJ), FractionalIdeal.count_inv]
    linarith [h v]
  have h2 := mul_le_mul_left h1 J
  rwa [inv_mul_cancel_right₀ hJ, one_mul] at h2

theorem mem_iff_valuation {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (x : K) :
    x ∈ I ↔ ∀ v : HeightOneSpectrum R,
      v.valuation K x ≤ WithZero.exp (-FractionalIdeal.count K v I) := by
  by_cases hx : x = 0
  · subst hx
    simp [FractionalIdeal.zero_mem]
  have hs : FractionalIdeal.spanSingleton R⁰ x ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hx
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  simp only [valuation_eq_count K _ hx, WithZero.exp_le_exp, neg_le_neg_iff]
  exact ⟨fun h v => FractionalIdeal.count_mono K v hs h, le_of_count K hs hI⟩

theorem one_le_count {I : Ideal R} (hI : I ≠ ⊥) (v : HeightOneSpectrum R) (h : I ≤ v.asIdeal) :
    1 ≤ FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) := by
  rw [← FractionalIdeal.count_self K v]
  exact FractionalIdeal.count_mono K v (FractionalIdeal.coeIdeal_ne_zero.2 hI)
    ((FractionalIdeal.coeIdeal_le_coeIdeal K).2 h)

theorem sup_eq_top_of {I J : Ideal R} (hI : I ≠ ⊥)
    (h : ∀ v : HeightOneSpectrum R, I ≤ v.asIdeal → J ≤ v.asIdeal → False) : I ⊔ J = ⊤ := by
  by_contra H
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ H
  have h1 : I ≤ p := le_sup_left.trans hle
  exact h ⟨p, hp.isPrime, fun e => hI (le_bot_iff.1 (e ▸ h1))⟩ h1 (le_sup_right.trans hle)

theorem count_prod_pow (s : Finset (HeightOneSpectrum R)) (n : HeightOneSpectrum R → ℕ)
    (f : HeightOneSpectrum R → HeightOneSpectrum R) (hf : ∀ Q, f (f Q) = Q)
    (hs : ∀ Q, Q ∉ s → n Q = 0) (P : HeightOneSpectrum R) :
    FractionalIdeal.count K P ((∏ Q ∈ s, (f Q).asIdeal ^ n Q : Ideal R) : FractionalIdeal R⁰ K)
      = n (f P) := by
  classical
  have e : ((∏ Q ∈ s, (f Q).asIdeal ^ n Q : Ideal R) : FractionalIdeal R⁰ K)
      = ∏ Q ∈ s, ((f Q).asIdeal : FractionalIdeal R⁰ K) ^ n Q := by
    have := map_prod (FractionalIdeal.coeIdealHom R⁰ K) (fun Q => (f Q).asIdeal ^ n Q) s
    simp only [map_pow] at this
    exact this
  rw [e, FractionalIdeal.count_prod K P _ _
    (fun Q _ => pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (f Q).ne_bot)),
    Finset.sum_eq_single (f P)]
  · rw [hf, FractionalIdeal.count_pow_self]
  · intro Q _ hQ
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal_coprime, mul_zero]
    rintro rfl
    exact hQ (hf Q).symm
  · intro h
    rw [hs _ h, pow_zero, FractionalIdeal.count_one]

end general

theorem exists_numerator : ∀ (E : Type) [Field E] [NumberField E] (σ : 𝓞 E ≃+* 𝓞 E) (cp : HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 E)), (∀ x, σ (σ x) = x) → (∀ Q x, x ∈ (cp Q).asIdeal ↔ σ x ∈ Q.asIdeal) → ∀ δ : HeightOneSpectrum (𝓞 E) → ℤ, (Function.support δ).Finite → (∀ Q, δ (cp Q) = -δ Q) → ∃ cc : Ideal (𝓞 E), cc ≠ ⊥ ∧ cc ⊔ cc.map (σ : 𝓞 E →+* 𝓞 E) = ⊤ ∧ (∀ Q, FractionalIdeal.count E Q (cc : FractionalIdeal (𝓞 E)⁰ E) = max (δ Q) 0) ∧ (∀ b : 𝓞 E, (∀ Q, δ Q ≠ 0 → b ∉ Q.asIdeal) → cc ⊔ Ideal.span {b} = ⊤) ∧ ∀ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ WithZero.exp (-δ Q)) → J * idlE (cc.map (σ : 𝓞 E →+* 𝓞 E)) = idlE cc := by
  intro E _ _ σ cp hσ hcp δ hfin hanti
  have hinv : ∀ Q, cp (cp Q) = Q := fun Q => by
    ext x
    rw [hcp, hcp, hσ]
  have hmap : ∀ Q : HeightOneSpectrum (𝓞 E),
      Q.asIdeal.map (σ : 𝓞 E →+* 𝓞 E) = (cp Q).asIdeal := fun Q => by
    ext x
    rw [hcp, Ideal.mem_map_iff_of_surjective (σ : 𝓞 E →+* 𝓞 E) σ.surjective]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [hσ] using hy
    · intro h
      exact ⟨σ x, h, hσ x⟩
  set s := hfin.toFinset with hsdef
  have hs : ∀ Q, Q ∉ s → (δ Q).toNat = 0 := fun Q hQ => by
    have : δ Q = 0 := by simpa [hsdef] using hQ
    simp [this]
  set cc : Ideal (𝓞 E) := ∏ Q ∈ s, Q.asIdeal ^ (δ Q).toNat with hcc
  have hbar : cc.map (σ : 𝓞 E →+* 𝓞 E) = ∏ Q ∈ s, (cp Q).asIdeal ^ (δ Q).toNat := by
    have := map_prod (Ideal.mapHom (σ : 𝓞 E →+* 𝓞 E)) (fun Q => Q.asIdeal ^ (δ Q).toNat) s
    simp only [map_pow, Ideal.mapHom_apply, hmap] at this
    exact this
  have h0 : cc ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun Q _ => pow_ne_zero _ Q.ne_bot
  have h0' : cc.map (σ : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    rw [hbar]
    exact Finset.prod_ne_zero_iff.2 fun Q _ => pow_ne_zero _ (cp Q).ne_bot
  have hc : ∀ Q, FractionalIdeal.count E Q (cc : FractionalIdeal (𝓞 E)⁰ E) = max (δ Q) 0 :=
    fun Q => by
      rw [← Int.ofNat_toNat]
      exact count_prod_pow E s (fun Q => (δ Q).toNat) id (fun _ => rfl) hs Q
  have hc' : ∀ Q, FractionalIdeal.count E Q
      ((cc.map (σ : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = max (-δ Q) 0 :=
    fun Q => by
      rw [← hanti, ← Int.ofNat_toNat, hbar]
      exact count_prod_pow E s (fun Q => (δ Q).toNat) cp hinv hs Q
  refine ⟨cc, h0, sup_eq_top_of h0 fun v h1 h2 => ?_, hc, fun b hb => sup_eq_top_of h0 fun v h1 h2 => ?_,
    fun J hJ => ?_⟩
  · have a1 := one_le_count E h0 v h1
    have a2 := one_le_count E h0' v h2
    rw [hc] at a1
    rw [hc'] at a2
    omega
  · have a1 := one_le_count E h0 v h1
    rw [hc] at a1
    exact hb v (by omega) ((Ideal.span_singleton_le_iff_mem _).1 h2)
  · have f0 : (cc : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h0
    have f0' : ((cc.map (σ : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.2 h0'
    have hJD : J = (((cc : FractionalIdeal (𝓞 E)⁰ E) *
        ((cc.map (σ : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ :
          FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
      ext x
      rw [hJ, FractionalIdeal.mem_coe, mem_iff_valuation E (mul_ne_zero f0 (inv_ne_zero f0'))]
      refine forall_congr' fun Q => ?_
      rw [FractionalIdeal.count_mul E Q f0 (inv_ne_zero f0'), FractionalIdeal.count_inv, hc, hc']
      have : max (δ Q) 0 + -max (-δ Q) 0 = δ Q := by omega
      rw [this]
    have hid : ∀ I : Ideal (𝓞 E),
        idlE I = ((I : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := fun _ => rfl
    rw [hJD, hid, hid, ← FractionalIdeal.coe_mul, inv_mul_cancel_right₀ f0']

end GlobalTheory.NumeratorIdeal
