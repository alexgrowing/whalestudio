import Mathlib

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.Wd

open PowerSeries

variable {O LL : Type} [CommRing O] [IsDomain O] [Field LL] [Algebra O LL]
  (hinj : Function.Injective (algebraMap O LL)) (l : O)
  (ψ : PowerSeries O →+* PowerSeries LL) (hψC : ∀ o : O, ψ (PowerSeries.C o) = PowerSeries.C (algebraMap O LL o))
  (u : PowerSeries LL) (hu : IsUnit u) (hψ : ψ (PowerSeries.X + PowerSeries.C l) = PowerSeries.X * u)
include hinj hψC hu hψ

theorem dvd_cancel_unit {k : ℕ} {f : PowerSeries LL} (h : PowerSeries.X ^ k ∣ u * f) :
    PowerSeries.X ^ k ∣ f := by
  have dvd_of_dvd_isUnit_mul_lemma {R : Type _} [CommRing R] {u f g : R} (hu : IsUnit u)
      (h : g ∣ u * f) : g ∣ f := by
    obtain ⟨v, rfl⟩ := hu
    have e : f = ↑v⁻¹ * (↑v * f) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [e]
    exact dvd_mul_of_dvd_right h _
  exact
       dvd_of_dvd_isUnit_mul_lemma hu h

omit hinj hψC hψ in
theorem dvd_cancel_unit' {k : ℕ} {f : PowerSeries LL} (h : PowerSeries.X ^ k ∣ u * f) :
    PowerSeries.X ^ k ∣ f := by
  have dvd_of_dvd_isUnit_mul_lemma {R : Type _} [CommRing R] {u f g : R} (hu : IsUnit u)
      (h : g ∣ u * f) : g ∣ f := by
    obtain ⟨v, rfl⟩ := hu
    have e : f = ↑v⁻¹ * (↑v * f) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [e]
    exact dvd_mul_of_dvd_right h _
  exact
       dvd_of_dvd_isUnit_mul_lemma hu h

theorem poly_eq_zero : ∀ (k : ℕ) (r : Polynomial O), r.degree < k →
    PowerSeries.X ^ k ∣ ψ (r : PowerSeries O) → r = 0 := by
  have dvd_of_dvd_isUnit_mul_lemma {R : Type _} [CommRing R] {u f g : R} (hu : IsUnit u)
      (h : g ∣ u * f) : g ∣ f := by
    obtain ⟨v, rfl⟩ := hu
    have e : f = ↑v⁻¹ * (↑v * f) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [e]
    exact dvd_mul_of_dvd_right h _
  have hψX : ψ PowerSeries.X = PowerSeries.X * u - PowerSeries.C (algebraMap O LL l) := by
    have h := hψ
    rw [map_add, hψC] at h
    exact eq_sub_of_add_eq h
  intro k
  induction k with
  | zero =>
    intro r hr _
    by_contra hr0
    rw [Polynomial.degree_eq_natDegree hr0] at hr
    have h0 : r.natDegree < 0 := by exact_mod_cast hr
    omega
  | succ k ih =>
    intro r hr hdvd
    have hmon : (Polynomial.X + Polynomial.C l : Polynomial O).Monic := Polynomial.monic_X_add_C l
    have hrem : Polynomial.modByMonic r (Polynomial.X + Polynomial.C l) = Polynomial.C (r.eval (-l)) := by
      have hg : (Polynomial.X + Polynomial.C l : Polynomial O) = Polynomial.X - Polynomial.C (-l) := by
        rw [map_neg, sub_neg_eq_add]
      rw [hg]
      exact Polynomial.modByMonic_X_sub_C_eq_C_eval r (-l)
    have hsplit : r = Polynomial.C (r.eval (-l)) +
        (Polynomial.X + Polynomial.C l) * Polynomial.divByMonic r (Polynomial.X + Polynomial.C l) := by
      have h1 : Polynomial.modByMonic r (Polynomial.X + Polynomial.C l) +
          (Polynomial.X + Polynomial.C l) * Polynomial.divByMonic r (Polynomial.X + Polynomial.C l) = r := by
        first
          | exact Polynomial.modByMonic_add_div r (Polynomial.X + Polynomial.C l)
          | exact Polynomial.modByMonic_add_div r _ hmon
          | exact Polynomial.modByMonic_add_div r hmon
      rw [hrem] at h1
      exact h1.symm
    have hqdeg : (Polynomial.divByMonic r (Polynomial.X + Polynomial.C l)).degree < k := by
      by_cases hq0 : Polynomial.divByMonic r (Polynomial.X + Polynomial.C l) = 0
      · rw [hq0, Polynomial.degree_zero]
        first
          | exact WithBot.bot_lt_coe _
          | simp
      · have hr0 : r ≠ 0 := by
          rintro rfl
          exact hq0 (Polynomial.zero_divByMonic _)
        have hpos : 0 < (Polynomial.X + Polynomial.C l : Polynomial O).degree := by
          first
            | (rw [Polynomial.degree_X_add_C]; exact zero_lt_one)
            | simp
        have h1 : (Polynomial.divByMonic r (Polynomial.X + Polynomial.C l)).degree < r.degree := by
          first
            | exact Polynomial.degree_divByMonic_lt r (Polynomial.X + Polynomial.C l) hr0 hpos
            | exact Polynomial.degree_divByMonic_lt r _ hmon hr0 hpos
            | exact Polynomial.degree_divByMonic_lt r hmon hr0 hpos
        rw [Polynomial.degree_eq_natDegree hq0, Polynomial.degree_eq_natDegree hr0] at h1
        rw [Polynomial.degree_eq_natDegree hr0] at hr
        rw [Polynomial.degree_eq_natDegree hq0]
        have a1 : (Polynomial.divByMonic r (Polynomial.X + Polynomial.C l)).natDegree < r.natDegree := by
          exact_mod_cast h1
        have a2 : r.natDegree < k + 1 := by exact_mod_cast hr
        have a3 : (Polynomial.divByMonic r (Polynomial.X + Polynomial.C l)).natDegree < k := by omega
        exact_mod_cast a3
    obtain ⟨c, q, hrq, hq⟩ : ∃ (c : O) (q : Polynomial O),
        r = Polynomial.C c + (Polynomial.X + Polynomial.C l) * q ∧ q.degree < k :=
      ⟨_, _, hsplit, hqdeg⟩
    have hψr : ψ (r : PowerSeries O) =
        PowerSeries.C (algebraMap O LL c) + PowerSeries.X * (u * ψ (q : PowerSeries O)) := by
      rw [hrq]
      first
        | (simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X,
            map_add, map_mul, hψC, hψX]; ring)
        | (simp [hψC, hψX]; ring)
    have hX : PowerSeries.X ∣ ψ (r : PowerSeries O) :=
      (dvd_pow_self _ (Nat.succ_ne_zero k)).trans hdvd
    rw [hψr, PowerSeries.X_dvd_iff] at hX
    first
      | simp only [map_add, map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
          zero_mul, add_zero] at hX
      | simp at hX
    have hc0 : c = 0 := hinj (hX.trans (map_zero _).symm)
    simp only [hc0, map_zero, zero_add] at hψr
    rw [hψr, pow_succ'] at hdvd
    have h2 : PowerSeries.X ^ k ∣ u * ψ (q : PowerSeries O) :=
      (mul_dvd_mul_iff_left PowerSeries.X_ne_zero).mp hdvd
    have hq0 : q = 0 := ih q hq (dvd_of_dvd_isUnit_mul_lemma hu h2)
    rw [hrq, hc0, hq0]
    simp

theorem dvd_of_dvd_image [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : l ∈ IsLocalRing.maximalIdeal O) (k : ℕ) (a : PowerSeries O)
    (ha : PowerSeries.X ^ k ∣ ψ a) : (PowerSeries.X + PowerSeries.C l) ^ k ∣ a := by
  have hres : PowerSeries.map (IsLocalRing.residue O) ((PowerSeries.X + PowerSeries.C l) ^ k) =
      PowerSeries.X ^ k := by
    rw [map_pow, map_add, PowerSeries.map_X, PowerSeries.map_C,
      (IsLocalRing.residue_eq_zero_iff l).mpr hlm, map_zero, add_zero]
  have hg : PowerSeries.map (IsLocalRing.residue O) ((PowerSeries.X + PowerSeries.C l) ^ k) ≠ 0 := by
    rw [hres]; exact pow_ne_zero _ PowerSeries.X_ne_zero
  obtain ⟨q, r, hdiv⟩ := PowerSeries.exists_isWeierstrassDivision (f := a) hg
  have hdeg : r.degree < k := by
    have h := hdiv.degree_lt
    have hz : Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) l = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hlm
    first
      | simpa [hz, PowerSeries.order_X_pow] using h
      | simpa [hz] using h
      | (rw [hres, PowerSeries.order_X_pow, ENat.toNat_coe] at h; exact h)
      | (simp only [hres, PowerSeries.order_X_pow, ENat.toNat_coe] at h; exact h)
      | simpa [hres] using h
  have hψa : ψ a = (PowerSeries.X * u) ^ k * ψ q + ψ (r : PowerSeries O) := by
    rw [hdiv.eq_mul_add, map_add, map_mul, map_pow, hψ]
  have h1 : PowerSeries.X ^ k ∣ (PowerSeries.X * u) ^ k * ψ q :=
    dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (dvd_mul_right _ _) k) _
  have h2 : PowerSeries.X ^ k ∣ ψ (r : PowerSeries O) := by
    rw [hψa] at ha
    first
      | exact (dvd_add_right h1).mp ha
      | simpa using dvd_sub ha h1
  have hr0 : r = 0 := poly_eq_zero hinj l ψ hψC u hu hψ k r hdeg h2
  rw [hdiv.eq_mul_add, hr0, Polynomial.coe_zero, add_zero]
  exact dvd_mul_right _ _

end Formalism.MainNotions.N.Pv.LocalLengthBound.Wd
