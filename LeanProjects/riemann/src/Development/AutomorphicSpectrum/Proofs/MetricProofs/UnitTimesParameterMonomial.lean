import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero
import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc

noncomputable section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

theorem le_of_mul_pow_mem_span_pow {O : Type*} [CommRing O] [IsDomain O] {p a : O} (hp : Prime p)
    (ha : ¬ p ∣ a) {k n : ℕ} (h : a * p ^ k ∈ Ideal.span {p} ^ n) : n ≤ k := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  by_contra hlt
  have hlt' : k + 1 ≤ n := by omega
  have h1 : p ^ (k + 1) ∣ a * p ^ k := (pow_dvd_pow p hlt').trans h
  rw [pow_succ, mul_comm a, mul_comm (p ^ k) p, mul_comm p] at h1
  exact ha ((mul_dvd_mul_iff_left (pow_ne_zero k hp.ne_zero)).mp (by simpa [mul_comm] using h1))

theorem map_ptIdeal_eq_maximalIdeal_ordAff {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (hI : ∀ h ∈ I, eval t h = 0) [IsLocalRing (locRing I t)] :
    Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) = IsLocalRing.maximalIdeal (locRing I t) := by
  have hu := IrreducibleComponentPreimages.isUnit_algebraMap_locRing_iff I t hI
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu x]
    exact not_not.mpr (RingHom.mem_ker.mp hx)
  · intro x hx
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t x
    have ha : eval t a = 0 := by
      by_contra ha
      have h1 := (hu a).mpr ha
      rw [← hab] at h1
      exact (IsLocalRing.mem_maximalIdeal _).mp hx (isUnit_of_mul_isUnit_left h1)
    obtain ⟨v, hv⟩ := (hu b).mpr hb
    have hx' : x = algebraMap _ (locRing I t) a * ((v⁻¹ : (locRing I t)ˣ) : locRing I t) := by
      rw [← hab, ← hv]
      simp
    rw [hx']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr ha))

theorem exponent_eq_order_polynomial : ∀ (m e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)) (g : MvPolynomial (Fin m) ℂ) (u : (locRing I t)ˣ) (mm : Fin e → ℕ), (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → algebraMap _ (locRing I t) g = u * ∏ i ∈ Jf, algebraMap _ (locRing I t) (r i) ^ mm i → ∀ i ∈ Jf, ∀ n : ℕ, (∃ s ∉ SncRes.Par.chPrime I t (r i), s * g ∈ SncRes.Par.chPrime I t (r i) ^ n ⊔ I) ↔ n ≤ mm i := by
  intro m e I t r Jf g u mm hI hreg hdim hspan hg i hi n
  haveI := hreg
  haveI hdom : IsDomain (locRing I t) := isDomain_of_isRegularLocalRing
  have hu := IrreducibleComponentPreimages.isUnit_algebraMap_locRing_iff I t hI
  have hmax := map_ptIdeal_eq_maximalIdeal_ordAff I t hI
  have hspan' := hspan.trans hmax
  have hprime := prime_of_regular_params (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm
  have hnon := (regular_params_spec (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm).2
  have hp : Prime (algebraMap _ (locRing I t) (r i)) := hprime i
  have hkill : ∀ h ∈ I, algebraMap _ (locRing I t) h = 0 := fun h hh =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hh)
  constructor
  · rintro ⟨s, hs, hsg⟩
    have hs' : ¬ algebraMap _ (locRing I t) (r i) ∣ algebraMap _ (locRing I t) s := fun h =>
      hs (Ideal.mem_comap.mpr (Ideal.mem_span_singleton.mpr h))
    have hle : SncRes.Par.chPrime I t (r i) ^ n ⊔ I ≤
        (Ideal.span {algebraMap _ (locRing I t) (r i)} ^ n).comap (algebraMap _ (locRing I t)) := by
      refine sup_le ?_ ?_
      · rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
        exact Ideal.pow_right_mono Ideal.map_comap_le n
      · intro h hh
        rw [Ideal.mem_comap, hkill h hh]
        exact zero_mem _
    have hmap := Ideal.mem_comap.mp (hle hsg)
    have hprod := Finset.mul_prod_erase Jf (fun j => algebraMap _ (locRing I t) (r j) ^ mm j) hi
    refine le_of_mul_pow_mem_span_pow hp (a := algebraMap _ (locRing I t) s *
      (u * ∏ j ∈ Jf.erase i, algebraMap _ (locRing I t) (r j) ^ mm j)) ?_ ?_
    · intro hd
      rcases hp.dvd_or_dvd hd with h | h
      · exact hs' h
      rcases hp.dvd_or_dvd h with h | h
      · exact hp.not_unit (isUnit_of_dvd_unit h u.isUnit)
      · obtain ⟨j, hj, hd'⟩ := (Prime.dvd_finset_prod_iff hp _).mp h
        have hd'' := hp.dvd_of_dvd_pow hd'
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        exact hnon i j hji.symm (hp.associated_of_dvd (hprime j) hd'')
    · rw [map_mul, hg, ← hprod] at hmap
      convert hmap using 1
      ring
  · intro hn
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t (u : locRing I t)
    have hz : algebraMap _ (locRing I t) (b * g - a * ∏ j ∈ Jf, r j ^ mm j) = 0 := by
      simp only [map_sub, map_mul, map_prod, map_pow]
      rw [hg, ← hab]
      ring
    obtain ⟨c, hc, hcI⟩ := IrreducibleComponentPreimages.exists_mul_mem_of_algebraMap_locRing_eq_zero I t hz
    refine ⟨c * b, ?_, ?_⟩
    · intro hmem
      have h1 : algebraMap _ (locRing I t) (r i) ∣ algebraMap _ (locRing I t) (c * b) :=
        Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hmem)
      have h2 := (hu (c * b)).mpr (by rw [map_mul]; exact mul_ne_zero hc hb)
      exact hp.not_unit (isUnit_of_dvd_unit h1 h2)
    · have hri : r i ∈ SncRes.Par.chPrime I t (r i) :=
        Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _)
      have hpow : c * a * ∏ j ∈ Jf, r j ^ mm j ∈ SncRes.Par.chPrime I t (r i) ^ n := by
        apply Ideal.pow_le_pow_right hn
        obtain ⟨d, hd⟩ : r i ^ mm i ∣ ∏ j ∈ Jf, r j ^ mm j :=
          Finset.dvd_prod_of_mem (fun j => r j ^ mm j) hi
        rw [hd]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hri _))
      have hsplit : c * b * g = c * (b * g - a * ∏ j ∈ Jf, r j ^ mm j) +
          c * a * ∏ j ∈ Jf, r j ^ mm j := by ring
      rw [hsplit]
      exact Ideal.add_mem _ (Ideal.mem_sup_right hcI) (Ideal.mem_sup_left hpow)

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
