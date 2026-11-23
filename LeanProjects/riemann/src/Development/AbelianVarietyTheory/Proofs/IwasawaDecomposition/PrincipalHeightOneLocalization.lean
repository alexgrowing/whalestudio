import Mathlib
open IsLocalRing

namespace GlobalTheory

theorem pow_eq_of_associated_pow_irreducible {W : Type} [CommRing W] [IsDomain W] {ϖ : W}
    (hϖ : Irreducible ϖ) {k n : ℕ} (h : Associated (ϖ ^ k) (ϖ ^ n)) : k = n :=
  le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.dvd)
    ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.symm.dvd)

theorem associated_of_pow_associated_irreducible {W : Type} [CommRing W] [IsDomain W] {ϖ x : W}
    (hϖ : Irreducible ϖ) {j : ℕ} (hj : 1 ≤ j) (h : Associated (x ^ j) ϖ) : Associated x ϖ := by
  have hirr : Irreducible (x ^ j) := h.symm.irreducible hϖ
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rcases m with _ | m
  · simpa using h
  · exfalso
    rw [pow_succ] at hirr
    rcases hirr.isUnit_or_isUnit rfl with hu | hu
    · have hx : IsUnit x := isUnit_of_dvd_unit (dvd_pow_self x (Nat.succ_ne_zero m)) hu
      exact hirr.not_isUnit (hu.mul hx)
    · exact hirr.not_isUnit ((hu.pow (m + 1)).mul hu)

theorem span_map_localization_eq_maximalIdeal_pow {R : Type} [CommRing R] [IsDomain R]
    (Q : Ideal R) [Q.IsPrime] (hV : IsDiscreteValuationRing (Localization.AtPrime Q))
    {W : Type} [CommRing W] [IsDomain W] (ϖ : W) (hϖ : Irreducible ϖ) (g : R →+* W)
    (hg : Function.Injective g) (hu : ∀ r, r ∉ Q → IsUnit (g r))
    (hπ : ∃ π ∈ Q, Associated (g π) ϖ) (h : R) (hh : h ≠ 0) (n : ℕ)
    (hn : Associated (g h) (ϖ ^ n)) :
    (Ideal.span {h}).map (algebraMap R (Localization.AtPrime Q)) =
      maximalIdeal (Localization.AtPrime Q) ^ n := by
  obtain ⟨π₀, hπ₀Q, hπ₀⟩ := hπ
  let G : Localization.AtPrime Q →+* W :=
    IsLocalization.lift (M := Q.primeCompl) (S := Localization.AtPrime Q) (g := g)
      (fun y => hu y y.2)
  have hG : ∀ r, G (algebraMap R (Localization.AtPrime Q) r) = g r := fun r =>
    IsLocalization.lift_eq _ r
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime Q)
  have h2 : algebraMap R (Localization.AtPrime Q) π₀ ≠ 0 := by
    intro e
    apply hϖ.ne_zero
    exact hπ₀.eq_zero_iff.1 (by rw [← hG, e, map_zero])
  have h1 : algebraMap R (Localization.AtPrime Q) h ≠ 0 := by
    intro e
    apply hh
    apply hg
    rw [← hG, e, map_zero, map_zero]
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible h1 hp
  obtain ⟨j, hj⟩ := IsDiscreteValuationRing.associated_pow_irreducible h2 hp
  have hj1 : 1 ≤ j := by
    by_contra hj0
    have hj0' : j = 0 := by omega
    subst hj0'
    have hmem : algebraMap R (Localization.AtPrime Q) π₀ ∈ maximalIdeal (Localization.AtPrime Q) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q π₀).2 hπ₀Q
    rw [pow_zero, associated_one_iff_isUnit] at hj
    exact (IsLocalRing.mem_maximalIdeal _).1 hmem hj
  have hGp : Associated (G p) ϖ := by
    have := hj.map G
    rw [hG, map_pow] at this
    exact associated_of_pow_associated_irreducible hϖ hj1 (this.symm.trans hπ₀)
  have hk' : Associated (g h) (ϖ ^ k) := by
    have := hk.map G
    rw [hG, map_pow] at this
    exact this.trans (hGp.pow_pow)
  have hkn : k = n := pow_eq_of_associated_pow_irreducible hϖ (hk'.symm.trans hn)
  subst hkn
  rw [Ideal.map_span, Set.image_singleton, hp.maximalIdeal_eq, Ideal.span_singleton_pow]
  exact Ideal.span_singleton_eq_span_singleton.2 hk

end GlobalTheory
