import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.EmultiplicityPowSubOneOdd

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem gen_exists_nat {t : ℤ_[l]} (ht : IsUnit t) (d : ℤ_[l]) :
    ∃ j : ℕ, (l : ℤ_[l]) ∣ d + t * j := by
  have htz : PadicInt.toZMod t ≠ 0 := (ht.map PadicInt.toZMod).ne_zero
  refine ⟨(-(PadicInt.toZMod d) * (PadicInt.toZMod t)⁻¹ : ZMod l).val, ?_⟩
  have hm : d + t * ((-(PadicInt.toZMod d) * (PadicInt.toZMod t)⁻¹ : ZMod l).val : ℤ_[l]) ∈
      RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
    rw [RingHom.mem_ker, map_add, map_mul, map_natCast, ZMod.natCast_zmod_val]
    field_simp
    ring
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  exact hm

private theorem gen_emult {a : ℕ} (ha : 1 ≤ a) (ha2 : l = 2 → 2 ≤ a) {u : ℤ_[l]}
    (hu : emultiplicity (l : ℤ_[l]) (u - 1) = a) (n : ℕ) :
    emultiplicity (l : ℤ_[l]) (u ^ l ^ n - 1) = ((a + n : ℕ) : ℕ∞) := by
  have hlp : Prime l := Nat.prime_iff.mp Fact.out
  have h1 : (l : ℤ_[l]) ∣ u - 1 := by
    have := pow_dvd_of_le_emultiplicity (k := 1) (a := (l : ℤ_[l])) (b := u - 1)
      (by rw [hu]; exact_mod_cast ha)
    simpa using this
  by_cases hl : l = 2
  · have h2 : (l : ℤ_[l]) ^ 2 ∣ u - 1 :=
      pow_dvd_of_le_emultiplicity (by rw [hu]; exact_mod_cast ha2 hl)
    rw [emultiplicity_pow_sub_one_sq h2, hu, emultiplicity_pow_self_of_prime hlp]
    push_cast
    rfl
  · rw [emultiplicity_pow_sub_one_odd hl h1, hu, emultiplicity_pow_self_of_prime hlp]
    push_cast
    rfl

private theorem isUnit_padicInt_of_not_dvd {t : ℤ_[l]} (h : ¬ (l : ℤ_[l]) ∣ t) : IsUnit t := by
  by_contra hne
  have hm : t ∈ IsLocalRing.maximalIdeal ℤ_[l] := hne
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  exact h hm

private theorem exists_pow_eq_one_add_mul_sub_add_sq (v : ℤ_[l]) (j : ℕ) :
    ∃ c : ℤ_[l], v ^ j = 1 + (j : ℤ_[l]) * (v - 1) + (v - 1) ^ 2 * c := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨j + v * c, ?_⟩
    push_cast
    rw [pow_succ, hc]
    ring

private theorem gen_dvd {a : ℕ} (ha : 1 ≤ a) (ha2 : l = 2 → 2 ≤ a) {u : ℤ_[l]} (hunit : IsUnit u)
    (hu : emultiplicity (l : ℤ_[l]) (u - 1) = a) {x : ℤ_[l]} (hx : (l : ℤ_[l]) ^ a ∣ x - 1)
    (n : ℕ) : ∃ k : ℕ, (l : ℤ_[l]) ^ (a + n) ∣ u ^ k - x := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    rw [pow_zero, add_zero]
    have : (1 : ℤ_[l]) - x = -(x - 1) := by ring
    rw [this]
    exact (dvd_neg).mpr hx
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨d, hd⟩ := hk
    set v := u ^ l ^ n with hvdef
    have hv := gen_emult ha ha2 hu n
    have hvd : (l : ℤ_[l]) ^ (a' + 1 + n) ∣ v - 1 :=
      pow_dvd_of_le_emultiplicity (le_of_eq hv.symm)
    obtain ⟨t, ht⟩ := hvd
    have htu : IsUnit t := by
      apply isUnit_padicInt_of_not_dvd
      rintro ⟨s, hs⟩
      have hdv : (l : ℤ_[l]) ^ (a' + 1 + n + 1) ∣ v - 1 := ⟨s, by rw [ht, hs]; ring⟩
      have := le_emultiplicity_of_pow_dvd hdv
      rw [hv] at this
      norm_cast at this
      omega
    obtain ⟨j, e, he⟩ := gen_exists_nat ((hunit.pow k).mul htu) d
    obtain ⟨c, hc⟩ := exists_pow_eq_one_add_mul_sub_add_sq v j
    refine ⟨k + l ^ n * j, e + (l : ℤ_[l]) ^ (a' + n) * u ^ k * t ^ 2 * c, ?_⟩
    rw [pow_add, pow_mul, ← hvdef]
    linear_combination u ^ k * hc + hd + ((u ^ k) * j + u ^ k * c *
      (v - 1 + (l : ℤ_[l]) ^ (a' + 1 + n) * t)) * ht + (l : ℤ_[l]) ^ (a' + 1 + n) * he

theorem exists_pow_redPow_eq {a : ℕ} (ha : 1 ≤ a) (ha2 : l = 2 → 2 ≤ a) {u : ℤ_[l]ˣ}
    (hu : emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a) {x : ℤ_[l]ˣ} (hx : x ∈ princ l a) (b : ℕ) :
    ∃ k : ℕ, redPow l b (u ^ k) = redPow l b x := by
  rw [mem_princ] at hx
  obtain ⟨k, hk⟩ := gen_dvd ha ha2 u.isUnit hu hx b
  refine ⟨k, Units.ext ?_⟩
  have hkb : (l : ℤ_[l]) ^ b ∣ (u : ℤ_[l]) ^ k - x :=
    (pow_dvd_pow _ (Nat.le_add_left b a)).trans hk
  have hm : (u : ℤ_[l]) ^ k - x ∈ RingHom.ker (PadicInt.toZModPow b : ℤ_[l] →+* ZMod (l ^ b)) := by
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    exact hkb
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hm
  simpa [redPow] using hm

theorem princ_le_of_isClosed {a : ℕ} (ha : 1 ≤ a) (ha2 : l = 2 → 2 ≤ a) {U : Subgroup ℤ_[l]ˣ}
    (hU : IsClosed (U : Set ℤ_[l]ˣ)) {u : ℤ_[l]ˣ} (huU : u ∈ U)
    (hu : emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a) : princ l a ≤ U := by
  intro x hx
  refine mem_of_isClosed hU fun b => ?_
  obtain ⟨k, hk⟩ := exists_pow_redPow_eq ha ha2 hu hx b
  exact ⟨u ^ k, U.pow_mem huU k, hk⟩

end KStar.TotallyRealRoots
