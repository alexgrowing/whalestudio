import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

open GlobalTheory.IsoTriv

namespace GlobalTheory.IsoTriv.PrimeIdempotent

theorem mem_pow_of_map_dvd {R V : Type} [CommRing R] [IsDedekindDomain R] [CommRing V]
    [IsDomain V] [IsDiscreteValuationRing V] (φ : R →+* V) (b a : R) (hb : φ b ≠ 0) (n : ℕ)
    (hw : (Ideal.comap φ (IsLocalRing.maximalIdeal V)).IsMaximal)
    (hbn : b ∈ Ideal.comap φ (IsLocalRing.maximalIdeal V) ^ n) (z : V) (hz : φ a = φ b * z) :
    a ∈ Ideal.comap φ (IsLocalRing.maximalIdeal V) ^ n := by
  set w := Ideal.comap φ (IsLocalRing.maximalIdeal V) with hwdef
  by_cases ha : a = 0
  · rw [ha]; exact Ideal.zero_mem _
  have hspan : Ideal.span {a} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨J, hJ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hspan w
  generalize Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = i
    at hfac
  by_cases hi : n ≤ i
  · have h1 : a ∈ w ^ i * J := hfac ▸ Ideal.mem_span_singleton_self a
    exact Ideal.pow_le_pow_right hi (Ideal.mul_le_inf h1).1
  exfalso
  have hJw : ¬ J ≤ w := fun h => hw.ne_top (by rw [← hJ, sup_eq_left.mpr h])
  obtain ⟨s, hsJ, hsw⟩ := Set.not_subset.mp hJw
  have hb1 : b ∈ w ^ (i + 1) := Ideal.pow_le_pow_right (by omega) hbn
  have h2 : b * s ∈ Ideal.span {a} * w := by
    rw [hfac, mul_right_comm, ← pow_succ]
    exact Ideal.mul_mem_mul hb1 hsJ
  obtain ⟨m, hm, hm'⟩ := Ideal.mem_span_singleton_mul.mp h2
  apply hsw
  have h3 : φ s = z * φ m := by
    apply mul_left_cancel₀ hb
    rw [← map_mul, ← hm', map_mul, hz, mul_assoc]
  change φ s ∈ IsLocalRing.maximalIdeal V
  rw [h3]
  exact Ideal.mul_mem_left _ _ hm

theorem epsSt : EpsSt := by
  intro R V _ _ _ _ _ φ q hq hu
  set w := Ideal.comap φ (IsLocalRing.maximalIdeal V) with hwdef
  have hq0 : q ≠ 0 := fun h => hq (by rw [h, map_zero])
  have hqw : q ∈ w := (IsLocalRing.mem_maximalIdeal _).mpr hu
  have hwp : w.IsPrime := Ideal.comap_isPrime φ _
  have hw0 : w ≠ ⊥ := fun h => hq0 (by rw [h] at hqw; exact hqw)
  have hw : w.IsMaximal := hwp.isMaximal hw0
  have hspan : Ideal.span {q} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨J, hJ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hspan w
  generalize Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {q})) = e
    at hfac
  have hpow : ∀ M : ℕ, Ideal.span {q ^ M} = w ^ (e * M) * J ^ M := fun M => by
    rw [← Ideal.span_singleton_pow, hfac, mul_pow, pow_mul]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have key : ∀ N : ℕ, ∃ y ∈ J ^ N, ∃ z, φ y = 1 + φ q ^ N * z := by
    intro N
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible (pow_ne_zero N hq) hϖ
    have hco : w ^ k ⊔ J ^ N = ⊤ := Ideal.pow_sup_pow_eq_top hJ
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hco)
    have h1 : φ x ∈ Ideal.span {φ q ^ N} := by
      have h2 : φ x ∈ (Ideal.map φ w) ^ k := by
        rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem φ hx
      have h3 : φ x ∈ IsLocalRing.maximalIdeal V ^ k :=
        Ideal.pow_right_mono Ideal.map_comap_le k h2
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at h3
      rwa [Ideal.span_singleton_eq_span_singleton.mpr hk]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h1
    refine ⟨y, hy, -c, ?_⟩
    have h4 : φ x + φ y = 1 := by rw [← map_add, hxy, map_one]
    rw [← h4, hc]; ring
  choose ε hεJ hε using key
  refine ⟨ε, fun N => ⟨hε N, fun M hM a ⟨z, hz⟩ => ?_⟩⟩
  have hqM : q ^ M ∈ w ^ (e * M) := by
    have h1 : q ^ M ∈ w ^ (e * M) * J ^ M := hpow M ▸ Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf h1).1
  have ha : a ∈ w ^ (e * M) :=
    mem_pow_of_map_dvd φ (q ^ M) a (by rw [map_pow]; exact pow_ne_zero M hq) _ hw hqM z
      (by rw [map_pow]; exact hz)
  rw [hpow M, mul_comm (ε N)]
  exact Ideal.mul_mem_mul ha (Ideal.pow_le_pow_right hM (hεJ N))

end GlobalTheory.IsoTriv.PrimeIdempotent
