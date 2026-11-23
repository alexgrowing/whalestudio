import Mathlib
import Formalism.TameInertiaTowers.StatementField

open NumberField Ideal Polynomial

noncomputable section

namespace Formalism.TwoAdicCyclotomicDecomposition

theorem not_sq_in_cyclotomic_ring (K : Type*) [Field K] [NumberField K] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (p : ℕ) [hp : Fact p.Prime] (hpN : ¬ p ∣ N)
    (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) (X : 𝓞 K) (hX : X ^ 2 = ((p * m : ℤ) : 𝓞 K)) : False := by
  obtain ⟨⟨P, _, _⟩⟩ := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)
  have he : P.ramificationIdx ℤ = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K P hpN
  have hp0 : (span {(p : ℤ)}) ≠ ⊥ := by
    simp [hp.out.ne_zero]
  have he' : (span {(p : ℤ)}).ramificationIdx' P = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp0, he]
  have hpP : ((p : ℤ) : 𝓞 K) ∈ P := by
    have := (Ideal.over_def P (span {(p : ℤ)}))
    have h1 : (p : ℤ) ∈ P.under ℤ := by rw [← this]; exact mem_span_singleton_self _
    simpa using h1
  have hXP : X ∈ P := by
    apply (inferInstance : P.IsPrime).mem_of_pow_mem 2
    rw [hX, Int.cast_mul]
    exact P.mul_mem_right _ hpP
  have hX2 : X ^ 2 ∈ P ^ 2 := Ideal.pow_mem_pow hXP 2
  obtain ⟨s, t, hst⟩ : IsCoprime m (p : ℤ) := by
    exact ((Nat.prime_iff_prime_int.mp hp.out).irreducible.coprime_iff_not_dvd.mpr hm).symm
  have hp2 : ((p : ℤ) : 𝓞 K) ∈ P ^ 2 := by
    have : ((p : ℤ) : 𝓞 K) = (s : 𝓞 K) * X ^ 2 + (t : 𝓞 K) * (((p : ℤ) : 𝓞 K) * ((p : ℤ) : 𝓞 K)) := by
      rw [hX]
      have h' : ((s * m + t * p : ℤ) : 𝓞 K) = 1 := by rw [hst, Int.cast_one]
      push_cast at h' ⊢
      linear_combination (-(p : 𝓞 K)) * h'
    rw [this]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hX2) (Ideal.mul_mem_left _ _ ?_)
    rw [pow_two]; exact Ideal.mul_mem_mul hpP hpP
  have hle : map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) ≤ P ^ 2 := by
    rw [Ideal.map_span, span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff.mp hy]
    simpa using hp2
  have hB : BddAbove {k | map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) ≤ P ^ k} := by
    by_contra hB
    have := Nat.sSup_of_not_bddAbove hB
    unfold Ideal.ramificationIdx' at he'
    omega
  have := le_csSup hB (show 2 ∈ {k | map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) ≤ P ^ k} from hle)
  unfold Ideal.ramificationIdx' at he'
  omega

theorem not_sq_cyc (K : Type*) [Field K] [NumberField K] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) (x : K) (hx : x ^ 2 = ((p * m : ℤ) : K)) : False := by
  have hint : IsIntegral ℤ x := by
    refine ⟨X ^ 2 - C ((p * m : ℤ)), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hx, eq_intCast, sub_self]
  refine not_sq_in_cyclotomic_ring K N p hpN m hm ⟨x, hint⟩ ?_
  apply RingOfIntegers.ext
  exact hx

section Signs

variable {L : Type} [Field L] [NumberField L]

theorem pm_of_sq {x : L} {c : ℕ} (hx : x ^ 2 = -(c : L)) (σ : Gal(L/ℚ)) :
    σ x = x ∨ σ x = -x := by
  have : (σ x) ^ 2 = x ^ 2 := by rw [← map_pow, hx, map_neg, map_natCast]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp this

theorem ne_zero_of_sq {x : L} {c : ℕ} (hc : c ≠ 0) (hx : x ^ 2 = -(c : L)) : x ≠ 0 := by
  rintro rfl
  have : (c : L) = 0 := by
    have := hx.symm
    simpa using this
  exact hc (by exact_mod_cast this)

theorem ne_neg_self {x : L} (hx0 : x ≠ 0) : x ≠ -x := by
  intro h
  have : (2 : L) * x = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h2 | h2
  · exact two_ne_zero h2
  · exact hx0 h2

theorem sgn_of_eq {x : L} {ρ : Gal(L/ℚ)} (h : ρ x = x) : sgn ρ x = 1 := by
  simp [sgn, h]

theorem sgn_of_neg {x : L} (hx0 : x ≠ 0) {ρ : Gal(L/ℚ)} (h : ρ x = -x) : sgn ρ x = -1 := by
  have : ρ x ≠ x := by rw [h]; exact fun e => ne_neg_self hx0 e.symm
  simp [sgn, this]

theorem sgn_spec {x : L} (hx0 : x ≠ 0) {σ : Gal(L/ℚ)} (h : σ x = x ∨ σ x = -x) :
    σ x = (((sgn σ x : ℤˣ) : ℤ) : L) * x := by
  rcases h with h | h
  · rw [sgn_of_eq h, h]; simp
  · rw [sgn_of_neg hx0 h, h]; simp

theorem sgn_mul {x : L} (hx0 : x ≠ 0) (hpm : ∀ σ : Gal(L/ℚ), σ x = x ∨ σ x = -x)
    (σ τ : Gal(L/ℚ)) : sgn (σ * τ) x = sgn σ x * sgn τ x := by
  rcases hpm τ with hτ | hτ <;> rcases hpm σ with hσ | hσ
  · rw [sgn_of_eq hσ, sgn_of_eq hτ, sgn_of_eq (by rw [AlgEquiv.mul_apply, hτ, hσ])]; rfl
  · rw [sgn_of_neg hx0 hσ, sgn_of_eq hτ, sgn_of_neg hx0 (by rw [AlgEquiv.mul_apply, hτ, hσ])]; rfl
  · rw [sgn_of_eq hσ, sgn_of_neg hx0 hτ,
      sgn_of_neg hx0 (by rw [AlgEquiv.mul_apply, hτ, map_neg, hσ])]; rfl
  · rw [sgn_of_neg hx0 hσ, sgn_of_neg hx0 hτ,
      sgn_of_eq (by rw [AlgEquiv.mul_apply, hτ, map_neg, hσ, neg_neg])]; rfl

def sgnHom (x : L) (hx0 : x ≠ 0) (hpm : ∀ σ : Gal(L/ℚ), σ x = x ∨ σ x = -x) :
    Gal(L/ℚ) →* ℤˣ where
  toFun σ := sgn σ x
  map_one' := sgn_of_eq (by simp)
  map_mul' := sgn_mul hx0 hpm

end Signs

theorem klein_four_cover (u v w t : ℤˣ × ℤˣ) (hu : u.1 = -1) (hv : v.2 = -1) (hw : w.1 * w.2 = -1) :
    t = 1 ∨ t = u ∨ t = v ∨ t = w ∨ t = u * v ∨ t = u * w ∨ t = v * w := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  obtain ⟨w1, w2⟩ := w
  obtain ⟨t1, t2⟩ := t
  simp only at hu hv hw
  subst hu hv
  revert hw
  rcases Int.units_eq_one_or u2 with rfl | rfl <;> rcases Int.units_eq_one_or v1 with rfl | rfl <;>
    rcases Int.units_eq_one_or w1 with rfl | rfl <;> rcases Int.units_eq_one_or w2 with rfl | rfl <;>
    rcases Int.units_eq_one_or t1 with rfl | rfl <;> rcases Int.units_eq_one_or t2 with rfl | rfl <;>
    decide

section Layer

variable {L : Type} [Field L] [NumberField L] {n q d : ℕ} {ζ a b : L}

theorem layer_splitting (h : IsLayer n q d ζ a b) :
    IsSplittingField ℚ L ((X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ))) := by
  obtain ⟨hζ, ha, hb, htop⟩ := h
  have hquad : ∀ (x : L) (c : ℕ), x ^ 2 = -(c : L) → Splits (X ^ 2 + C (c : L)) := by
    intro x c hx
    have : (X ^ 2 + C (c : L)) = (X - C x) * (X + C x) := by
      have hc : C (c : L) = - C (x ^ 2) := by rw [hx, C_neg, neg_neg]
      rw [hc, C_pow]; ring
    rw [this]; exact (Splits.X_sub_C x).mul (Splits.X_add_C x)
  have hne : ((X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ)) : ℚ[X]) ≠ 0 :=
    (((monic_X_pow_sub_C 1 (pow_ne_zero _ two_ne_zero)).mul
      (monic_X_pow_add_C _ two_ne_zero)).mul (monic_X_pow_add_C _ two_ne_zero)).ne_zero
  constructor
  · have e : ((X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ)) : ℚ[X]).map
        (algebraMap ℚ L) = (X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : L)) * (X ^ 2 + C (d : L)) := by
      simp
    rw [e]
    exact ((X_pow_sub_one_splits hζ).mul (hquad a q ha)).mul (hquad b d hb)
  · rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← htop,
      IntermediateField.adjoin_toSubalgebra]
    apply Algebra.adjoin_mono
    intro x hx
    rw [mem_rootSet]
    refine ⟨hne, ?_⟩
    rcases hx with rfl | rfl | rfl
    · simp [hζ.pow_eq_one]
    · simp [ha]
    · simp [hb]

theorem layer_isGalois (h : IsLayer n q d ζ a b) : IsGalois ℚ L := by
  have := layer_splitting h
  have := Normal.of_isSplittingField (F := ℚ) (E := L)
    ((X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ)))
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

theorem layer_ext (h : IsLayer n q d ζ a b) {σ τ : Gal(L/ℚ)} (h1 : σ ζ = τ ζ) (h2 : σ a = τ a)
    (h3 : σ b = τ b) : σ = τ := by
  have htop : Algebra.adjoin ℚ ({ζ, a, b} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra, h.2.2.2, IntermediateField.top_toSubalgebra]
  apply AlgEquiv.coe_toAlgHom_injective
  apply AlgHom.ext_of_adjoin_eq_top htop
  intro x hx
  rcases hx with rfl | rfl | rfl
  · simpa using h1
  · simpa using h2
  · simpa using h3

theorem galMap_injective (h : IsLayer n q d ζ a b) (hq0 : q ≠ 0) (hd0 : d ≠ 0) :
    Function.Injective (galMap h.1 a b) := by
  intro σ τ hστ
  simp only [galMap, Prod.mk.injEq] at hστ
  obtain ⟨h1, h2, h3⟩ := hστ
  apply layer_ext h
  · rw [← h.1.autToPow_spec ℚ σ, ← h.1.autToPow_spec ℚ τ, h1]
  · rw [sgn_spec (ne_zero_of_sq hq0 h.2.1) (pm_of_sq h.2.1 σ),
      sgn_spec (ne_zero_of_sq hq0 h.2.1) (pm_of_sq h.2.1 τ), h2]
  · rw [sgn_spec (ne_zero_of_sq hd0 h.2.2.1) (pm_of_sq h.2.2.1 σ),
      sgn_spec (ne_zero_of_sq hd0 h.2.2.1) (pm_of_sq h.2.2.1 τ), h3]

theorem galMap_mul (h : IsLayer n q d ζ a b) (hq0 : q ≠ 0) (hd0 : d ≠ 0) (σ τ : Gal(L/ℚ)) :
    galMap h.1 a b (σ * τ) = galMap h.1 a b σ * galMap h.1 a b τ :=
  Prod.ext (map_mul _ σ τ) (Prod.ext
    (sgn_mul (ne_zero_of_sq hq0 h.2.1) (pm_of_sq h.2.1) σ τ)
    (sgn_mul (ne_zero_of_sq hd0 h.2.2.1) (pm_of_sq h.2.2.1) σ τ))

theorem card_galL (hn : 1 ≤ n) : Nat.card (GalL n) = 2 ^ (n + 1) := by
  rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Nat.prime_two (by omega), Nat.card_eq_fintype_card,
    Fintype.card_units_int]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

theorem layer_finrank_ge (h : IsLayer n q d ζ a b) (hn : 1 ≤ n) (hqd : HypOdd q d)
    [IsGalois ℚ L] : 2 ^ (n + 1) ≤ Module.finrank ℚ L := by
  obtain ⟨hζ, ha, hb, htop⟩ := h
  obtain ⟨hq, hd, hqd', hq2, hd2⟩ := hqd
  let K := IntermediateField.adjoin ℚ ({ζ} : Set L)
  have : IsCyclotomicExtension {2 ^ n} ℚ K := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hKdeg : Module.finrank ℚ K = 2 ^ (n - 1) := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral ζ),
      ← cyclotomic_eq_minpoly_rat hζ (by positivity), natDegree_cyclotomic,
      Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp
  have hns : ∀ (p : ℕ) (m : ℤ), p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ m → ∀ y : L, y ∈ K →
      y ^ 2 = ((p * m : ℤ) : L) → False := by
    intro p m hp hp2 hm y hy hy2
    have := Fact.mk hp
    have hpN : ¬ p ∣ 2 ^ n := fun hdvd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
    exact not_sq_cyc K (2 ^ n) p hpN m hm ⟨y, hy⟩ (by ext; simpa using hy2)
  have hndvd1 : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ -1 := by
    intro p hp hdvd
    have := Int.eq_one_of_dvd_one (by positivity) ((dvd_neg).mp hdvd)
    have : p = 1 := by exact_mod_cast this
    exact hp.one_lt.ne' this
  have hqd_dvd : ¬ (q : ℤ) ∣ (d : ℤ) := by
    intro hdvd
    have : q ∣ d := by exact_mod_cast hdvd
    exact hqd' ((Nat.prime_dvd_prime_iff_eq hq hd).mp this)
  have haK : a ∉ K := fun haK => hns q (-1) hq hq2 (hndvd1 q hq) a haK (by push_cast; rw [ha]; ring)
  have hbK : b ∉ K := fun hbK => hns d (-1) hd hd2 (hndvd1 d hd) b hbK (by push_cast; rw [hb]; ring)
  have habK : a * b ∉ K := fun habK => hns q d hq hq2 hqd_dvd (a * b) habK
    (by rw [mul_pow, ha, hb]; push_cast; ring)
  have hfix : IntermediateField.fixedField K.fixingSubgroup = K := IsGalois.fixedField_fixingSubgroup K
  have hmove : ∀ y : L, y ∉ K → ∃ σ ∈ K.fixingSubgroup, σ y ≠ y := by
    intro y hy
    by_contra hc
    push Not at hc
    apply hy
    rw [← hfix]
    exact (IntermediateField.mem_fixedField_iff _ _).mpr hc
  obtain ⟨σ1, hσ1, h1⟩ := hmove a haK
  obtain ⟨σ2, hσ2, h2⟩ := hmove b hbK
  obtain ⟨σ3, hσ3, h3⟩ := hmove (a * b) habK
  have ha0 := ne_zero_of_sq hq.ne_zero ha
  have hb0 := ne_zero_of_sq hd.ne_zero hb
  let s : Gal(L/ℚ) →* ℤˣ × ℤˣ := (sgnHom a ha0 (pm_of_sq ha)).prod (sgnHom b hb0 (pm_of_sq hb))
  have hs : ∀ σ, s σ = (sgn σ a, sgn σ b) := fun σ => rfl
  have hu : (s σ1).1 = -1 := by
    rw [hs]
    exact sgn_of_neg ha0 ((pm_of_sq ha σ1).resolve_left h1)
  have hv : (s σ2).2 = -1 := by
    rw [hs]
    exact sgn_of_neg hb0 ((pm_of_sq hb σ2).resolve_left h2)
  have hw : (s σ3).1 * (s σ3).2 = -1 := by
    rw [hs]
    rw [map_mul] at h3
    rcases pm_of_sq ha σ3 with e1 | e1 <;> rcases pm_of_sq hb σ3 with e2 | e2
    · exact absurd (by rw [e1, e2]) h3
    · rw [sgn_of_eq e1, sgn_of_neg hb0 e2]; rfl
    · rw [sgn_of_neg ha0 e1, sgn_of_eq e2]; rfl
    · exact absurd (by rw [e1, e2, neg_mul_neg]) h3
  let φ : K.fixingSubgroup → ℤˣ × ℤˣ := fun σ => s σ
  have hφ : Function.Surjective φ := by
    intro t
    rcases klein_four_cover (s σ1) (s σ2) (s σ3) t hu hv hw with e | e | e | e | e | e | e
    · exact ⟨1, by simp [φ, e]⟩
    · exact ⟨⟨σ1, hσ1⟩, e.symm⟩
    · exact ⟨⟨σ2, hσ2⟩, e.symm⟩
    · exact ⟨⟨σ3, hσ3⟩, e.symm⟩
    · exact ⟨⟨σ1, hσ1⟩ * ⟨σ2, hσ2⟩, by simp [φ, e]⟩
    · exact ⟨⟨σ1, hσ1⟩ * ⟨σ3, hσ3⟩, by simp [φ, e]⟩
    · exact ⟨⟨σ2, hσ2⟩ * ⟨σ3, hσ3⟩, by simp [φ, e]⟩
  have hH : 4 ≤ Nat.card K.fixingSubgroup := by
    have := Nat.card_le_card_of_surjective φ hφ
    rwa [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_units_int] at this
  have hLK : Module.finrank K L = Nat.card K.fixingSubgroup :=
    (IsGalois.card_fixingSubgroup_eq_finrank K).symm
  rw [← Module.finrank_mul_finrank ℚ K L, hKdeg, hLK]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  calc 2 ^ (k + 1 + 1) = 2 ^ k * 4 := by ring
    _ ≤ 2 ^ k * Nat.card K.fixingSubgroup := Nat.mul_le_mul_left _ hH

end Layer

theorem layerGalois : LayerGalois := by
  intro n q d hn hqd L _ _ ζ a b h
  have hG := layer_isGalois h
  have hq0 : q ≠ 0 := hqd.1.ne_zero
  have hd0 : d ≠ 0 := hqd.2.1.ne_zero
  have hinj := galMap_injective h hq0 hd0
  have hcard1 : Nat.card Gal(L/ℚ) = Module.finrank ℚ L := IsGalois.card_aut_eq_finrank ℚ L
  have hle : Nat.card Gal(L/ℚ) ≤ Nat.card (GalL n) := Nat.card_le_card_of_injective _ hinj
  have hge := layer_finrank_ge h hn hqd
  rw [card_galL hn] at hle
  refine ⟨hG, by omega, galMap_mul h hq0 hd0, hinj.bijective_of_nat_card_le ?_⟩
  rw [card_galL hn]
  omega

theorem layerExists : LayerExists := by
  intro n q d
  set f : ℚ[X] := cyclotomic (2 ^ n) ℚ * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ)) with hf
  let F := SplittingField f
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  have : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  have hmap' : ∀ φ : ℚ →+* F, f.map φ =
      cyclotomic (2 ^ n) F * (X ^ 2 + C (q : F)) * (X ^ 2 + C (d : F)) := by
    intro φ
    simp [f, map_cyclotomic, C_eq_natCast]
  have hmap := hmap' (algebraMap ℚ F)
  have hsp : Splits (f.map (algebraMap ℚ F)) := SplittingField.splits f
  rw [hmap] at hsp
  have hne : cyclotomic (2 ^ n) F * (X ^ 2 + C (q : F)) * (X ^ 2 + C (d : F)) ≠ 0 :=
    (((cyclotomic.monic _ F).mul (monic_X_pow_add_C _ two_ne_zero)).mul
      (monic_X_pow_add_C _ two_ne_zero)).ne_zero
  have hc : Splits (cyclotomic (2 ^ n) F) :=
    hsp.of_dvd hne (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
  have hqs : Splits (X ^ 2 + C (q : F)) :=
    hsp.of_dvd hne (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
  have hds : Splits (X ^ 2 + C (d : F)) := hsp.of_dvd hne (dvd_mul_left _ _)
  obtain ⟨ζ, hζ⟩ := hc.exists_eval_eq_zero (by
    rw [degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (by positivity)).ne')
  have hζp : IsPrimitiveRoot ζ (2 ^ n) := (isRoot_cyclotomic_iff_charZero (by positivity)).mp hζ
  obtain ⟨a, ha⟩ := hqs.exists_eval_eq_zero (by rw [degree_X_pow_add_C (by norm_num)]; norm_num)
  obtain ⟨b, hb⟩ := hds.exists_eval_eq_zero (by rw [degree_X_pow_add_C (by norm_num)]; norm_num)
  have ha2 : a ^ 2 = -(q : F) := by
    simp only [eval_add, eval_pow, eval_X, eval_C] at ha
    linear_combination ha
  have hb2 : b ^ 2 = -(d : F) := by
    simp only [eval_add, eval_pow, eval_X, eval_C] at hb
    linear_combination hb
  refine ⟨F, inferInstance, inferInstance, ζ, a, b, ?_⟩
  rw [show (DivisionRing.toRatAlgebra : Algebra ℚ F) = SplittingField.instAlgebra_1 f from
    Subsingleton.elim _ _]
  refine ⟨hζp, ha2, hb2, ?_⟩
  rw [← IntermediateField.toSubalgebra_inj, IntermediateField.adjoin_toSubalgebra,
    IntermediateField.top_toSubalgebra, eq_top_iff]
  refine (SplittingField.adjoin_rootSet f).symm.le.trans ?_
  rw [Algebra.adjoin_le_iff]
  intro x hx
  rw [mem_rootSet] at hx
  have hx' := hx.2
  rw [← eval_map_algebraMap, hmap'] at hx'
  simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C] at hx'
  rcases mul_eq_zero.mp hx' with hx' | hx'
  · rcases mul_eq_zero.mp hx' with hx' | hx'
    · have hxp : IsPrimitiveRoot x (2 ^ n) := (isRoot_cyclotomic_iff_charZero (by positivity)).mp hx'
      obtain ⟨i, -, hi⟩ := hζp.eq_pow_of_pow_eq_one hxp.pow_eq_one
      rw [← hi]
      exact pow_mem (Algebra.subset_adjoin (by simp)) i
    · have : x ^ 2 = a ^ 2 := by rw [ha2]; linear_combination hx'
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with rfl | rfl
      · exact Algebra.subset_adjoin (by simp)
      · exact neg_mem (Algebra.subset_adjoin (by simp))
  · have : x ^ 2 = b ^ 2 := by rw [hb2]; linear_combination hx'
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with rfl | rfl
    · exact Algebra.subset_adjoin (by simp)
    · exact neg_mem (Algebra.subset_adjoin (by simp))

end Formalism.TwoAdicCyclotomicDecomposition
