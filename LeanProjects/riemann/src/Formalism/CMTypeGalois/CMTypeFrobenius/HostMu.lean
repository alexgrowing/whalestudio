import Mathlib
import Formalism.CMTypeGalois.StatementField

open NumberField Polynomial

noncomputable section

namespace Formalism.Q3

namespace CMRootsOfUnity

variable {q : Fin 3 → ℕ}

lemma not_sq_d (hq : Hyp3 q) (d : ℤ) (S : Finset (Fin 3)) (hS : S.Nonempty ∨ d < 0)
    (hdq : ∀ i, ¬ (q i : ℤ) ∣ d) :
    ¬ IsSquare ((d : ℚ) * ∏ i ∈ S, (((-(q i : ℤ)) : ℤ) : ℚ)) := by
  classical
  rw [← Int.cast_prod, ← Int.cast_mul, Rat.isSquare_intCast_iff]
  rintro ⟨r, hr⟩
  rcases S.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
  · rcases hS with ⟨x, hx⟩ | hd
    · simp at hx
    · simp only [Finset.prod_empty, mul_one] at hr
      nlinarith [mul_self_nonneg r]
  · have hp : Prime (q i0 : ℤ) := Nat.prime_iff_prime_int.mp (hq.1 i0).1
    have hprod : d * ∏ i ∈ S, -(q i : ℤ) =
        -(q i0 : ℤ) * (d * ∏ i ∈ S.erase i0, -(q i : ℤ)) := by
      rw [← Finset.mul_prod_erase S (fun i => -(q i : ℤ)) hi0]; ring
    have hpr : (q i0 : ℤ) ∣ r := by
      apply hp.dvd_of_dvd_pow (n := 2)
      rw [sq, ← hr, hprod]
      exact Dvd.dvd.mul_right (dvd_neg.mpr dvd_rfl) _
    obtain ⟨t, rfl⟩ := hpr
    have h0 : (q i0 : ℤ) ≠ 0 := by exact_mod_cast (hq.1 i0).1.ne_zero
    have hrest : (q i0 : ℤ) ∣ d * ∏ i ∈ S.erase i0, -(q i : ℤ) := by
      refine ⟨-(t * t), ?_⟩
      rw [hprod] at hr
      apply mul_left_cancel₀ h0
      linear_combination -hr
    rcases hp.dvd_or_dvd hrest with h | h
    · exact hdq i0 h
    · obtain ⟨i, hi, hdiv⟩ := (hp.dvd_finsetProd_iff _).mp h
      rw [dvd_neg, Int.natCast_dvd_natCast,
        Nat.prime_dvd_prime_iff_eq (hq.1 i0).1 (hq.1 i).1] at hdiv
      exact (Finset.ne_of_mem_erase hi) (hq.2 hdiv).symm

lemma not_dvd_one (hq : Hyp3 q) (i : Fin 3) : ¬ (q i : ℤ) ∣ 1 := by
  intro h
  have h1 : q i ∣ 1 := by exact_mod_cast h
  exact (hq.1 i).1.one_lt.ne' (Nat.dvd_one.1 h1)

variable {E : Type} [Field E] [NumberField E] {α : Fin 3 → E}

lemma not_sq_in_E (hK : MQKummer) (hq : Hyp3 q) (hα : IsHost q α) (d : ℤ) (hd : d < 0)
    (hdq : ∀ i, ¬ (q i : ℤ) ∣ d) : ¬ IsSquare (d : E) := by
  intro h
  have hns : ∀ S : Finset (Fin 3), S.Nonempty →
      ¬ IsSquare (∏ i ∈ S, (((-(q i : ℤ)) : ℤ) : ℚ)) := by
    intro S hS
    have := not_sq_d hq 1 S (Or.inl hS) (fun i => by simpa using not_dvd_one hq i)
    simpa using this
  obtain ⟨_, _, hsq⟩ := hK 3 E (fun i => -(q i : ℤ)) α hα hns
  have h' : IsSquare (algebraMap ℚ E (d : ℚ)) := by simpa using h
  obtain ⟨S, hS⟩ := (hsq d).1 h'
  exact not_sq_d hq d S (Or.inr hd) hdq hS

lemma gal_sq (hH : HostGalois) (hq : Hyp3 q) (hα : IsHost q α) (σ : Gal(E/ℚ)) :
    σ * σ = 1 := by
  obtain ⟨_, _, hbij, hmul⟩ := hH q hq E α hα
  apply hbij.1
  rw [hmul]
  funext i
  have h1 : galSign α (1 : Gal(E/ℚ)) i = 1 := by simp [galSign]
  rw [Pi.mul_apply, h1, Int.units_mul_self]

lemma no_prime_root (hH : HostGalois) (hq : Hyp3 q) (hα : IsHost q α) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (η : E) (hη : IsPrimitiveRoot η p) : False := by
  obtain ⟨hGal, _, _, _⟩ := hH q hq E α hα
  have := hGal
  have hpos := hp.pos
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have hη2 : IsPrimitiveRoot (η ^ 2) p := hη.pow_of_coprime 2 hcop
  have hmin : minpoly ℚ (η ^ 2) = minpoly ℚ η := by
    rw [← cyclotomic_eq_minpoly_rat hη hpos, ← cyclotomic_eq_minpoly_rat hη2 hpos]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := E)).1 hmin
  have hσ' : σ η = η ^ 2 := hσ
  have hsq := gal_sq hH hq hα σ
  have h4 : η = η ^ 4 := by
    calc η = (σ * σ) η := by rw [hsq]; rfl
    _ = σ (σ η) := rfl
    _ = η ^ 4 := by rw [hσ', map_pow, hσ', ← pow_mul]
  have h3 : η ^ 3 = 1 := by
    have hne : η ≠ 0 := hη.ne_zero hp.ne_zero
    apply mul_left_cancel₀ hne
    linear_combination -h4
  have h5 := (hη.pow_eq_one_iff_dvd 3).1 h3
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h5)

lemma no_four (hK : MQKummer) (hq : Hyp3 q) (hα : IsHost q α) (η : E)
    (hη : IsPrimitiveRoot η 4) : False := by
  have h2 : IsPrimitiveRoot (η ^ 2) 2 := hη.pow (by norm_num) (by norm_num)
  have h := h2.eq_neg_one_of_two_right
  refine not_sq_in_E hK hq hα (-1) (by norm_num) (fun i hi => not_dvd_one hq i ?_)
    ⟨η, by push_cast; linear_combination -h⟩
  exact dvd_neg.1 hi

lemma no_three (hK : MQKummer) (hq : Hyp3 q) (hq3 : ∀ i, q i ≠ 3) (hα : IsHost q α) (ω : E)
    (hω : IsPrimitiveRoot ω 3) : False := by
  have h3 : ω ^ 3 = 1 := hω.pow_eq_one
  have h1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hs : ω ^ 2 + ω + 1 = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) h1
    · exact h
  refine not_sq_in_E hK hq hα (-3) (by norm_num) (fun i hi => ?_)
    ⟨2 * ω + 1, by push_cast; linear_combination (-4) * hs⟩
  have h3' : q i ∣ 3 := by
    have := dvd_neg.1 hi
    exact_mod_cast this
  exact hq3 i ((Nat.prime_dvd_prime_iff_eq (hq.1 i).1 Nat.prime_three).1 h3')

end CMRootsOfUnity

open CMRootsOfUnity

theorem hostMu_of (hK : MQKummer) (hH : HostGalois) : HostMu := by
  intro q hq hq3 E _ _ α hα ζ ⟨n, hn, hζn⟩
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hζn⟩
  have hmpos : 0 < orderOf ζ := orderOf_pos_iff.2 hfin
  have hprim : IsPrimitiveRoot ζ (orderOf ζ) := IsPrimitiveRoot.orderOf ζ
  have hodd : ∀ {p : ℕ}, p.Prime → p ∣ orderOf ζ → p = 2 := by
    intro p hp hpm
    obtain ⟨k, hk⟩ := hpm
    have hη : IsPrimitiveRoot (ζ ^ k) p := hprim.pow hmpos (by rw [hk, mul_comm])
    by_contra hp2
    by_cases hp3 : p = 3
    · subst hp3
      exact no_three hK hq hq3 hα (ζ ^ k) hη
    · exact no_prime_root hH hq hα p hp hp2 hp3 (ζ ^ k) hη
  have h4 : ¬ 4 ∣ orderOf ζ := by
    rintro ⟨k, hk⟩
    exact no_four hK hq hα (ζ ^ k) (hprim.pow hmpos (by rw [hk, mul_comm]))
  have hm2 : orderOf ζ ∣ 2 := by
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hmpos.ne' hodd
    rw [hpow] at h4 ⊢
    rcases h : (orderOf ζ).primeFactorsList.length with _ | _ | a
    · simp
    · simp
    · exfalso
      rw [h] at h4
      exact h4 (by
        have : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [this]
        exact pow_dvd_pow 2 (by omega))
  have hζ2 : ζ * ζ = 1 := by
    rw [← sq]
    exact (hprim.pow_eq_one_iff_dvd 2).2 hm2
  exact mul_self_eq_one_iff.1 hζ2

end Formalism.Q3
