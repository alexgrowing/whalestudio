import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal

set_option autoImplicit false

noncomputable section

open NumberField UniqueFactorizationMonoid Formalism.L2.Pj

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam

variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {k : Type} [Field k] [Algebra V k]
  [IsFractionRing V k]

theorem vV_alg_nonneg (v : V) : 0 ≤ vV V (algebraMap V k v) := by
  have hle : valV V (K' := k) (algebraMap V k v) ≤ 1 := by
    unfold valV
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ v
  unfold vV
  by_cases h0 : valV V (K' := k) (algebraMap V k v) = 0
  · rw [h0, WithZero.log_zero]; simp
  · have := (WithZero.log_le_log h0 one_ne_zero).2 hle
    rw [WithZero.log_one] at this
    linarith

theorem int_mem_range (ψ : E →+* k) (x : 𝓞 E) : ψ (x : E) ∈ (algebraMap V k).range := by
  have h1 : IsIntegral ℤ (ψ (x : E)) := (RingOfIntegers.isIntegral_coe x).map ψ.toIntAlgHom
  have h2 : IsIntegral V (ψ (x : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨y, hy⟩

theorem w_nonneg (ψ : E →+* k) (x : 𝓞 E) : 0 ≤ vV V (ψ (x : E)) := by
  obtain ⟨y, hy⟩ := int_mem_range (V := V) ψ x
  rw [← hy]
  exact vV_alg_nonneg y

def primeOf (ψ : E →+* k) (hψ : Function.Injective ψ) : Ideal (𝓞 E) where
  carrier := {x | 0 < vV V (ψ (x : E)) ∨ x = 0}
  add_mem' := by
    intro a b ha hb
    change 0 < vV V (ψ (a : E)) ∨ a = 0 at ha
    change 0 < vV V (ψ (b : E)) ∨ b = 0 at hb
    change 0 < vV V (ψ ((a + b : 𝓞 E) : E)) ∨ a + b = 0
    have key : ∀ z : k, z ≠ 0 → (0 < vV V z ↔ valV V (K' := k) z < 1) := by
      intro z hz
      have hz' : valV V (K' := k) z ≠ 0 := (valV V (K' := k)).ne_zero_iff.mpr hz
      unfold vV
      constructor
      · intro h
        apply not_le.mp
        intro h1
        have h2 := (WithZero.log_le_log one_ne_zero hz').mpr h1
        rw [WithZero.log_one] at h2
        linarith
      · intro h
        by_contra hc
        have hc' := not_lt.mp hc
        have h2 : WithZero.log (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.log (valV V (K' := k) z) := by
          rw [WithZero.log_one]
          linarith
        exact absurd ((WithZero.log_le_log one_ne_zero hz').mp h2) (not_le.mpr h)
    have cz : ∀ z : 𝓞 E, z ≠ 0 → ψ (z : E) ≠ 0 := fun z hz => (map_ne_zero ψ).mpr (by exact_mod_cast hz)
    by_cases hab : a + b = 0
    · exact Or.inr hab
    left
    by_cases ha0 : a = 0
    · subst ha0
      rw [zero_add] at hab ⊢
      exact hb.resolve_right hab
    by_cases hb0 : b = 0
    · subst hb0
      rw [add_zero] at hab ⊢
      exact ha.resolve_right hab
    have ha' := ha.resolve_right ha0
    have hb' := hb.resolve_right hb0
    rw [key _ (cz _ hab)]
    have hsum : ((a + b : 𝓞 E) : E) = (a : E) + (b : E) := by simp
    rw [hsum, map_add]
    calc valV V (K' := k) (ψ (a : E) + ψ (b : E))
        ≤ max (valV V (K' := k) (ψ (a : E))) (valV V (K' := k) (ψ (b : E))) := (valV V (K' := k)).map_add _ _
      _ < 1 := max_lt ((key _ (cz a ha0)).mp ha') ((key _ (cz b hb0)).mp hb')
  zero_mem' := Or.inr rfl
  smul_mem' := by
    intro c x hx
    change 0 < vV V (ψ (x : E)) ∨ x = 0 at hx
    change 0 < vV V (ψ ((c • x : 𝓞 E) : E)) ∨ c • x = 0
    rw [smul_eq_mul]
    by_cases hcx : c * x = 0
    · exact Or.inr hcx
    left
    have hc : c ≠ 0 := left_ne_zero_of_mul hcx
    have hx0 : x ≠ 0 := right_ne_zero_of_mul hcx
    have hxv : 0 < vV V (ψ (x : E)) := hx.resolve_right hx0
    have hcE : ψ (c : E) ≠ 0 := (map_ne_zero ψ).mpr (by exact_mod_cast hc)
    have hxE : ψ (x : E) ≠ 0 := (map_ne_zero ψ).mpr (by exact_mod_cast hx0)
    have hmul : ((c * x : 𝓞 E) : E) = (c : E) * (x : E) := by simp
    have hcv := w_nonneg (V := V) ψ c
    rw [hmul, map_mul]
    unfold vV at hcv hxv ⊢
    rw [map_mul, WithZero.log_mul ((valV V (K' := k)).ne_zero_iff.mpr hcE)
      ((valV V (K' := k)).ne_zero_iff.mpr hxE)]
    linarith

variable (V) in
theorem mem_primeOf (ψ : E →+* k) (hψ : Function.Injective ψ) (x : 𝓞 E) :
    x ∈ primeOf (V := V) ψ hψ ↔ 0 < vV V (ψ (x : E)) ∨ x = 0 := Iff.rfl

theorem psi_ne_zero (ψ : E →+* k) (hψ : Function.Injective ψ) {x : 𝓞 E} (hx : x ≠ 0) : ψ (x : E) ≠ 0 := by
  exact (map_ne_zero ψ).2 (by exact_mod_cast hx)

theorem primeOf_isPrime (ψ : E →+* k) (hψ : Function.Injective ψ) : (primeOf (V := V) ψ hψ).IsPrime := by
  have hmul : ∀ a b : k, a ≠ 0 → b ≠ 0 → vV V (a * b) = vV V a + vV V b := by
    intro a b ha hb
    unfold vV
    rw [map_mul, WithZero.log_mul ((valV V (K' := k)).ne_zero_iff.mpr ha)
      ((valV V (K' := k)).ne_zero_iff.mpr hb)]
    ring
  have hv1 : vV V (1 : k) = 0 := by
    unfold vV; rw [map_one, WithZero.log_one]; simp
  refine Ideal.isPrime_iff.2 ⟨(Ideal.ne_top_iff_one _).2 ?_, ?_⟩
  · rw [mem_primeOf]
    push_neg
    refine ⟨?_, one_ne_zero⟩
    simp [hv1]
  · intro x y hxy
    rw [mem_primeOf] at hxy ⊢
    rw [mem_primeOf]
    by_cases hx0 : x = 0
    · exact Or.inl (Or.inr hx0)
    by_cases hy0 : y = 0
    · exact Or.inr (Or.inr hy0)
    have hxy' := hxy.resolve_right (mul_ne_zero hx0 hy0)
    have hc : ((x * y : 𝓞 E) : E) = (x : E) * (y : E) := by simp
    rw [hc, map_mul, hmul _ _ (psi_ne_zero ψ hψ hx0) (psi_ne_zero ψ hψ hy0)] at hxy'
    by_contra hno
    push_neg at hno
    have := hno.1.1
    have := hno.2.1
    linarith

theorem w_zero_of_not_mem (ψ : E →+* k) (hψ : Function.Injective ψ) {x : 𝓞 E}
    (hx : x ∉ primeOf (V := V) ψ hψ) : vV V (ψ (x : E)) = 0 := by
  rw [mem_primeOf] at hx
  push_neg at hx
  exact le_antisymm hx.1 (w_nonneg ψ x)

theorem mem_factors_of_mem {P : Ideal (𝓞 E)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) {x : 𝓞 E} (hx0 : x ≠ 0) (hx : x ∈ P) :
    0 < (normalizedFactors (Ideal.span {x})).count P := by
  have hspan : Ideal.span {x} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx0
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  have hdvd : P ∣ Ideal.span {x} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hx)
  obtain ⟨Q, hQ, hPQ⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hspan hirr hdvd
  rw [associated_iff_eq] at hPQ
  rw [hPQ]
  exact Multiset.count_pos.2 hQ

theorem count_zero_of_not_mem {P : Ideal (𝓞 E)} {x : 𝓞 E} (hx : x ∉ P) :
    (normalizedFactors (Ideal.span {x})).count P = 0 := by
  refine Multiset.count_eq_zero.2 fun hP => hx ?_
  have hdvd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
  exact (Ideal.le_of_dvd hdvd) (Ideal.mem_span_singleton_self x)

theorem count_mul_span {P : Ideal (𝓞 E)} {x y : 𝓞 E} (hx : x ≠ 0) (hy : y ≠ 0) :
    (normalizedFactors (Ideal.span {x * y})).count P =
      (normalizedFactors (Ideal.span {x})).count P + (normalizedFactors (Ideal.span {y})).count P := by
  have hx' : Ideal.span {x} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx
  have hy' : Ideal.span {y} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hy
  rw [← Ideal.span_singleton_mul_span_singleton, UniqueFactorizationMonoid.normalizedFactors_mul hx' hy',
    Multiset.count_add]

theorem w_eq_count (ψ : E →+* k) (hψ : Function.Injective ψ) (hP0 : primeOf (V := V) ψ hψ ≠ ⊥) :
    ∃ π : 𝓞 E, π ≠ 0 ∧ ∀ (n : ℕ) (x : 𝓞 E), x ≠ 0 →
      (normalizedFactors (Ideal.span {x})).count (primeOf (V := V) ψ hψ) = n →
      vV V (ψ (x : E)) = n * vV V (ψ (π : E)) := by
  set P := primeOf (V := V) ψ hψ with hPdef
  have hPp : P.IsPrime := primeOf_isPrime ψ hψ
  have hmulv : ∀ a b : 𝓞 E, a ≠ 0 → b ≠ 0 →
      vV V (ψ ((a * b : 𝓞 E) : E)) = vV V (ψ (a : E)) + vV V (ψ (b : E)) := by
    intro a b ha hb
    have hab : ((a * b : 𝓞 E) : E) = (a : E) * (b : E) := by simp
    rw [hab, map_mul]
    unfold vV
    rw [map_mul, WithZero.log_mul ((valV V (K' := k)).ne_zero_iff.mpr (psi_ne_zero ψ hψ ha))
      ((valV V (K' := k)).ne_zero_iff.mpr (psi_ne_zero ψ hψ hb))]
    ring
  have hspan : ∀ z : 𝓞 E, z ≠ 0 → Ideal.span {z} ≠ 0 := fun z hz => by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hz
  have hP2 : P ^ 2 < P := by
    refine lt_of_le_of_ne (Ideal.pow_le_self two_ne_zero) fun heq => ?_
    have h1 : P * P = P * ⊤ := by rw [← sq, heq, Ideal.mul_top]
    exact hPp.ne_top (mul_left_cancel₀ (by rwa [Ne, Ideal.zero_eq_bot]) h1)

  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hP2
  have hπ0 : π ≠ 0 := by rintro rfl; exact hπ2 (Submodule.zero_mem _)
  have hcπ : (normalizedFactors (Ideal.span {π})).count P = 1 := by
    have h1 := mem_factors_of_mem hPp hP0 hπ0 hπP
    by_contra hne
    apply hπ2
    have h2 : Multiset.replicate 2 P ≤ normalizedFactors (Ideal.span {π}) := by
      rw [Multiset.le_iff_count]
      intro Q
      rw [Multiset.count_replicate]
      split_ifs with hQ
      · subst hQ; omega
      · exact Nat.zero_le _
    have h3 : P ^ 2 ∣ Ideal.span {π} := by
      have := Multiset.prod_dvd_prod_of_le h2
      rw [Multiset.prod_replicate] at this
      exact this.trans (UniqueFactorizationMonoid.prod_normalizedFactors (hspan π hπ0)).dvd
    exact (Ideal.le_of_dvd h3) (Ideal.mem_span_singleton_self π)

  obtain ⟨A, hA⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hπP)
  have hAP : ¬ A ≤ P := by
    intro hle
    have hdvd : P ∣ A := Ideal.dvd_iff_le.2 hle
    have h4 : P * P ∣ Ideal.span {π} := hA ▸ mul_dvd_mul_left P hdvd
    apply hπ2
    rw [sq]
    exact (Ideal.le_of_dvd h4) (Ideal.mem_span_singleton_self π)
  obtain ⟨s, hsA, hsP⟩ := Set.not_subset.1 hAP
  have hs0 : s ≠ 0 := by rintro rfl; exact hsP (Submodule.zero_mem _)
  have hws : vV V (ψ (s : E)) = 0 := w_zero_of_not_mem ψ hψ hsP
  have hcs : (normalizedFactors (Ideal.span {s})).count P = 0 := count_zero_of_not_mem hsP
  refine ⟨π, hπ0, ?_⟩
  intro n
  induction n with
  | zero =>
    intro x hx hc
    have hxP : x ∉ P := fun hxP => by
      have := mem_factors_of_mem hPp hP0 hx hxP
      omega
    simp [w_zero_of_not_mem ψ hψ hxP]
  | succ n ih =>
    intro x hx hc
    have hxP : x ∈ P := by
      by_contra hxP
      rw [count_zero_of_not_mem hxP] at hc
      omega
    have hmem : x * s ∈ Ideal.span {π} := by rw [hA]; exact Ideal.mul_mem_mul hxP hsA
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hy
      exact mul_ne_zero hx hs0 hy.symm
    have hcy : (normalizedFactors (Ideal.span {y})).count P = n := by
      have h1 := count_mul_span (P := P) hy0 hπ0
      rw [hy, count_mul_span hx hs0, hc, hcs, hcπ] at h1
      omega
    have h2 := hmulv y π hy0 hπ0
    rw [hy, hmulv x s hx hs0, hws, ih y hy0 hcy] at h2
    push_cast
    linarith

theorem exists_delta_count {P : Ideal (𝓞 E)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ∃ δ : 𝓞 E, δ ∈ differentIdeal ℤ (𝓞 E) ∧ δ ≠ 0 ∧
      (normalizedFactors (Ideal.span {δ})).count P = (normalizedFactors (differentIdeal ℤ (𝓞 E))).count P := by
  set Dif := differentIdeal ℤ (𝓞 E) with hDif
  have hD0 : Dif ≠ ⊥ := differentIdeal_ne_bot

  have hlt : Dif * P < Dif := by
    refine lt_of_le_of_ne Ideal.mul_le_left fun heq => ?_
    have h1 : Dif * P = Dif * ⊤ := by rw [heq, Ideal.mul_top]
    have := mul_left_cancel₀ (by rwa [Ne, Ideal.zero_eq_bot]) h1
    exact hP.ne_top this
  obtain ⟨δ, hδD, hδP⟩ := SetLike.exists_of_lt hlt
  have hδ0 : δ ≠ 0 := by rintro rfl; exact hδP (Submodule.zero_mem _)
  refine ⟨δ, hδD, hδ0, ?_⟩

  obtain ⟨K, hK⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hδD)
  have hKP : ¬ K ≤ P := by
    intro hle
    apply hδP
    have : Ideal.span {δ} ≤ Dif * P := by rw [hK]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self δ)
  have hK0 : K ≠ 0 := by
    rintro rfl
    rw [mul_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at hK
    exact hδ0 hK
  have hcK : (normalizedFactors K).count P = 0 := by
    refine Multiset.count_eq_zero.2 fun hP' => hKP ?_
    exact Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP')
  rw [hK, UniqueFactorizationMonoid.normalizedFactors_mul (by rwa [Ne, Ideal.zero_eq_bot]) hK0,
    Multiset.count_add, hcK, add_zero]

theorem exists_delta_val [IsGalois ℚ E] (ℓ a m : ℕ) (hℓ : ℓ.Prime) (hm : ¬ ℓ ∣ m)
    (hdisc : (discr E).natAbs = ℓ ^ a * m) (ψ : E →+* k) (hψ : Function.Injective ψ)
    (hℓψ : 0 < vV V (ψ (ℓ : E))) :
    ∃ δ : 𝓞 E, δ ∈ differentIdeal ℤ (𝓞 E) ∧ δ ≠ 0 ∧
      vV V (ψ (δ : E)) * Module.finrank ℚ E = a * vV V (ψ (ℓ : E)) := by
  set P := primeOf (V := V) ψ hψ
  have hPp : P.IsPrime := primeOf_isPrime ψ hψ
  have hℓ0 : (ℓ : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hℓ.ne_zero
  have hℓP : (ℓ : 𝓞 E) ∈ P := Or.inl (by simpa using hℓψ)
  have hP0 : P ≠ ⊥ := fun h => hℓ0 (by rw [h] at hℓP; exact (Submodule.mem_bot _).1 hℓP)
  obtain ⟨π, hπ0, hw⟩ := w_eq_count ψ hψ hP0
  obtain ⟨δ, hδD, hδ0, hδc⟩ := exists_delta_count hPp hP0
  have hex := diffExp E ℓ a m hℓ hm hdisc P hPp hℓP
  have h1 := hw _ δ hδ0 rfl
  have h2 := hw _ (ℓ : 𝓞 E) hℓ0 rfl
  refine ⟨δ, hδD, hδ0, ?_⟩
  have e : ((ℓ : 𝓞 E) : E) = (ℓ : E) := by simp
  rw [e] at h2
  rw [h1, h2, hδc]
  have hex' : ((normalizedFactors (differentIdeal ℤ (𝓞 E))).count P : ℤ) * Module.finrank ℚ E =
      a * (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).count P := by exact_mod_cast hex
  linear_combination vV V (ψ (π : E)) * hex'

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
