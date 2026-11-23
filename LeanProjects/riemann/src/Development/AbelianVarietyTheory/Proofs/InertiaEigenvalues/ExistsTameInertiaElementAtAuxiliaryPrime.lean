import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.TwSys.InertiaElt

open Filter Topology

theorem exists_coprime_dvd_mul_pow (m : ℕ) (o : ℕ) (ho : o ≠ 0) : ∃ t K : ℕ, Nat.Coprime t m ∧ o ∣ t * m ^ K := by
  induction o using Nat.recOnMul with
  | zero => exact absurd rfl ho
  | one => exact ⟨1, 0, Nat.coprime_one_left m, one_dvd _⟩
  | prime p hp =>
    by_cases h : p ∣ m
    · exact ⟨1, 1, Nat.coprime_one_left m, by simpa using h⟩
    · exact ⟨p, 0, (Nat.Prime.coprime_iff_not_dvd hp).2 h, by simp⟩
  | mul a b iha ihb =>
    obtain ⟨t, K, ht, hK⟩ := iha (left_ne_zero_of_mul ho)
    obtain ⟨t', K', ht', hK'⟩ := ihb (right_ne_zero_of_mul ho)
    refine ⟨t * t', K + K', Nat.Coprime.mul_left ht ht', ?_⟩
    have : t * t' * m ^ (K + K') = (t * m ^ K) * (t' * m ^ K') := by ring
    rw [this]
    exact mul_dvd_mul hK hK'

theorem exists_limit_pow {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (σ : Γ) (m : ℕ) : ∃ z : Γ, (∀ I : Subgroup Γ, IsClosed (I : Set Γ) → σ ∈ I → z ∈ I) ∧
      (∀ U : Subgroup Γ, IsOpen (U : Set Γ) → ∃ k : ℕ, z⁻¹ * σ ^ (m ^ k) ∈ U) ∧
      ∀ U : Subgroup Γ, IsOpen (U : Set Γ) → U.Normal → ∃ n : ℕ, Nat.Coprime n m ∧ z ^ n ∈ U := by
  obtain ⟨z, hz⟩ : ∃ z : Γ, MapClusterPt z atTop (fun k : ℕ => σ ^ (m ^ k)) :=
    exists_clusterPt_of_compactSpace (map (fun k : ℕ => σ ^ (m ^ k)) atTop)
  have key : ∀ U : Subgroup Γ, IsOpen (U : Set Γ) → ∃ᶠ k : ℕ in atTop, z⁻¹ * σ ^ (m ^ k) ∈ U := by
    intro U hU
    have ho : IsOpen ((fun x : Γ => z⁻¹ * x) ⁻¹' (U : Set Γ)) := hU.preimage (by fun_prop)
    exact hz.frequently (p := fun x => z⁻¹ * x ∈ U) (ho.mem_nhds (by simp))
  refine ⟨z, fun I hI hσ => ?_, fun U hU => (key U hU).exists, fun U hU hN => ?_⟩
  · exact hI.mem_of_mapClusterPt hz (Eventually.of_forall fun k => I.pow_mem hσ _)
  · have : Finite (Γ ⧸ U) := U.quotient_finite_of_isOpen hU
    obtain ⟨t, K, ht, hK⟩ := exists_coprime_dvd_mul_pow m (orderOf (QuotientGroup.mk' U σ)) (orderOf_pos _).ne'
    obtain ⟨k, hk, hmem⟩ := frequently_atTop.1 (key U hU) K
    refine ⟨t, ht, ?_⟩
    have e : QuotientGroup.mk' U z = QuotientGroup.mk' U σ ^ (m ^ k) := by
      rw [← map_pow]
      exact QuotientGroup.eq.2 hmem
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' U (z ^ t) = 1
    rw [map_pow, e, ← pow_mul, ← orderOf_dvd_iff_pow_eq_one]
    refine hK.trans ?_
    rw [mul_comm]
    exact Nat.mul_dvd_mul_right (pow_dvd_pow m hk) t

theorem isUnit_sub_one {O : Type*} [CommRing O] [IsDomain O] {n : ℕ} {ζ : O} (hn : IsUnit (n : O))
    (h : IsPrimitiveRoot ζ n) (h1 : 1 < n) : IsUnit (ζ - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 + 1 := ⟨n - 2, by omega⟩
  have e := h.prod_one_sub_pow_eq_order
  rw [Finset.prod_range_succ'] at e
  have hu : IsUnit (1 - ζ ^ (0 + 1)) := by
    refine isUnit_of_mul_isUnit_right (x := ∏ j ∈ Finset.range k, (1 - ζ ^ (j + 1 + 1))) ?_
    rw [e]
    exact_mod_cast hn
  rw [← neg_sub]
  simpa using hu.neg

theorem exists_place_mem (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 E) := by
    intro h
    have h2 : IsUnit (Algebra.norm ℤ ((p : ℕ) : 𝓞 E)) := h.map _
    have e : Algebra.norm ℤ ((p : ℕ) : 𝓞 E) = (p : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      rw [← Algebra.norm_algebraMap]
      simp
    rw [e, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h2
    exact hp.one_lt.ne' h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 E)}) (by
    rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : ((p : ℕ) : 𝓞 E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hmem))

end GlobalTheory.TwSys.InertiaElt

open GlobalTheory.TwSys.InertiaElt in

theorem GlobalTheory.TwSys.exists_tameInertiaElementAtAuxiliaryPrime : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
    (i : X.Tw), ∃ z, IsTameInertiaElementAtTwistPrime X i z := by
  intro D N X i
  have hl : (X.l i).Prime := (X.lPrime i).out
  obtain ⟨v, hv⟩ : ∃ v, v ∈ X.pD i := by
    have hp : (if X.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
      split_ifs
      · exact D.host.pde'_prime
      · exact D.host.pde_prime
    obtain ⟨v, hv⟩ := exists_place_mem D.host.E hp
    refine ⟨v, ?_⟩
    rw [← Finset.mem_coe, X.pD_eq i]
    exact hv
  obtain ⟨A, hA⟩ := exists_isPlaceOver N.Om v

  obtain ⟨p, hp, hp15, hp2, hpl⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ 15 ∧ p ≠ 2 ∧ p ≠ X.l i := by
    by_cases h : X.l i = 3
    · exact ⟨5, by norm_num, by norm_num, by norm_num, by omega⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, fun h' => h h'.symm⟩
  have : Fact p.Prime := ⟨hp⟩
  have hcard := X.delta_15 i v hv A hA
  have : Finite ((Ine (F := D.host.E) A).map (X.delta i)) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨⟨y, hy⟩, hyo⟩ := exists_prime_orderOf_dvd_card' (G := (Ine (F := D.host.E) A).map (X.delta i)) p
    (by rw [hcard]; exact hp15)
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hy
  have hord : orderOf (X.delta i σ) = p := by
    rw [← hyo, ← Subgroup.orderOf_coe]
  obtain ⟨z, hz1, hz2, hz3⟩ := exists_limit_pow σ (X.l i * Ideal.absNorm v.asIdeal)
  refine ⟨z, v, hv, A, hA, hz1 _ (isClosed_Ine A) hσ, ?_, hz3⟩
  obtain ⟨k, hk⟩ := hz2 _ (X.delta_open i)
  have hz : X.delta i z = X.delta i σ ^ ((X.l i * Ideal.absNorm v.asIdeal) ^ k) := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, inv_mul_eq_one] at hk
    exact hk
  have hpl' : Nat.Coprime p (X.l i) := (Nat.coprime_primes hp hl).2 hpl
  have hpq : Nat.Coprime p (Ideal.absNorm v.asIdeal) := by
    refine Nat.Coprime.coprime_dvd_left hp15 ?_
    have := X.delta_tame i v hv
    rw [Nat.Coprime, Nat.gcd_rec, this]
    norm_num
  have hprim : IsPrimitiveRoot (X.delta i σ) p := hord ▸ IsPrimitiveRoot.orderOf _
  have hcop : Nat.Coprime ((X.l i * Ideal.absNorm v.asIdeal) ^ k * 2) p :=
    Nat.Coprime.symm (Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (Nat.Coprime.mul_right hpl' hpq))
      ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have hprim2 : IsPrimitiveRoot (((X.delta i z : (X.O0 i)ˣ) : X.O0 i) ^ 2) p := by
    have := hprim.pow_of_coprime _ hcop
    rw [pow_mul, ← hz] at this
    rw [← Units.val_pow_eq_pow_val]
    exact IsPrimitiveRoot.coe_units_iff.2 this
  refine isUnit_sub_one ?_ hprim2 hp.one_lt
  have hlnu : ¬ IsUnit ((X.l i : ℕ) : X.O0 i) := by
    intro h
    have h2 := h.map (algebraMap (X.O0 i) (X.O i))
    rw [map_natCast] at h2
    exact X.O_l i h2
  have hc : IsCoprime ((p : ℕ) : X.O0 i) ((X.l i : ℕ) : X.O0 i) := hpl'.cast
  obtain ⟨a, b, hab⟩ := hc
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (hab ▸ isUnit_one) with h | h
  · exact isUnit_of_mul_isUnit_right h
  · exact absurd (isUnit_of_mul_isUnit_right h) hlnu
