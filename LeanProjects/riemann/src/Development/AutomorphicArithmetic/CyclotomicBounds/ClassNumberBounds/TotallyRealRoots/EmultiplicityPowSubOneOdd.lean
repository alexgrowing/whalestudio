import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LeNuIffPowMemPrinc

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem lte_not_dvd_natCast {m : ℕ} (hm : ¬ l ∣ m) : ¬ (l : ℤ_[l]) ∣ (m : ℤ_[l]) := by
  rintro ⟨c, hc⟩
  apply hm
  have h := congrArg PadicInt.toZMod hc
  rw [map_mul, map_natCast, map_natCast, ZMod.natCast_self, zero_mul] at h
  exact (ZMod.natCast_eq_zero_iff m l).mp h

private theorem lte_not_dvd_of_dvd_sub_one {u : ℤ_[l]} (hu : (l : ℤ_[l]) ∣ u - 1) :
    ¬ (l : ℤ_[l]) ∣ u := by
  intro h
  have h1 : (l : ℤ_[l]) ∣ 1 := by
    have := dvd_sub h hu
    rwa [sub_sub_cancel] at this
  exact PadicInt.prime_p.not_unit (isUnit_of_dvd_one h1)

private theorem lte_reduce {u : ℤ_[l]} (hu : (l : ℤ_[l]) ∣ u - 1)
    (h : ∀ k : ℕ, emultiplicity (l : ℤ_[l]) (u ^ l ^ k - 1) =
      emultiplicity (l : ℤ_[l]) (u - 1) + k) (n : ℕ) :
    emultiplicity (l : ℤ_[l]) (u ^ n - 1) =
      emultiplicity (l : ℤ_[l]) (u - 1) + emultiplicity l n := by
  rcases n with - | n
  · simp
  have hfin : FiniteMultiplicity l (n + 1) :=
    Nat.finiteMultiplicity_iff.mpr ⟨(Fact.out : l.Prime).ne_one, n.succ_pos⟩
  rcases emultiplicity_eq_coe.mp hfin.emultiplicity_eq_multiplicity with ⟨⟨c, hc⟩, hnot⟩
  set k := multiplicity l (n + 1) with hk
  have hcl : ¬ l ∣ c := by
    rintro ⟨d, rfl⟩
    exact hnot ⟨d, by rw [hc, pow_succ, mul_assoc]⟩
  have hx : (l : ℤ_[l]) ∣ u ^ l ^ k - 1 := by
    have := sub_dvd_pow_sub_pow u 1 (l ^ k)
    rw [one_pow] at this
    exact hu.trans this
  have e : u ^ (l ^ k * c) - 1 = (u ^ l ^ k) ^ c - 1 ^ c := by rw [one_pow, pow_mul]
  rw [hfin.emultiplicity_eq_multiplicity, ← hk]
  conv_lhs => rw [hc, e]
  rw [emultiplicity_pow_sub_pow_of_prime PadicInt.prime_p hx (lte_not_dvd_of_dvd_sub_one hx)
    (lte_not_dvd_natCast hcl), h k]

theorem emultiplicity_pow_sub_one_odd (hl : l ≠ 2) {u : ℤ_[l]} (hu : (l : ℤ_[l]) ∣ u - 1) (n : ℕ) :
    emultiplicity (l : ℤ_[l]) (u ^ n - 1) =
      emultiplicity (l : ℤ_[l]) (u - 1) + emultiplicity l n := by
  refine lte_reduce hu (fun k => ?_) n
  have h := emultiplicity_pow_prime_pow_sub_pow_prime_pow (p := l) (x := u) (y := 1)
    PadicInt.prime_p ((Fact.out : l.Prime).odd_of_ne_two hl) hu (lte_not_dvd_of_dvd_sub_one hu) k
  rwa [one_pow] at h

private theorem lte_two_step (hl : l = 2) {w : ℤ_[l]} (hw : (l : ℤ_[l]) ^ 2 ∣ w - 1) :
    emultiplicity (l : ℤ_[l]) (w ^ l - 1) = emultiplicity (l : ℤ_[l]) (w - 1) + 1 := by
  subst hl
  have hp : Prime ((2 : ℕ) : ℤ_[2]) := PadicInt.prime_p
  have h2 : ((2 : ℕ) : ℤ_[2]) ∣ w - 1 := (dvd_pow_self _ two_ne_zero).trans hw
  rw [show w ^ 2 - 1 = (w - 1) * (w + 1) by ring, emultiplicity_mul hp]
  congr 1
  rw [← Nat.cast_one (R := ℕ∞)]
  refine emultiplicity_eq_coe.2 ⟨?_, ?_⟩
  · rw [pow_one, show w + 1 = (w - 1) + ((2 : ℕ) : ℤ_[2]) by push_cast; ring]
    exact dvd_add h2 (dvd_refl _)
  · rw [one_add_one_eq_two]
    intro h
    have h3 := dvd_sub h hw
    rw [show (w + 1) - (w - 1) = ((2 : ℕ) : ℤ_[2]) * 1 by push_cast; ring, pow_two,
      mul_dvd_mul_iff_left hp.ne_zero] at h3
    exact hp.not_unit (isUnit_of_dvd_one h3)

theorem emultiplicity_pow_sub_one_sq {u : ℤ_[l]} (hu : (l : ℤ_[l]) ^ 2 ∣ u - 1) (n : ℕ) :
    emultiplicity (l : ℤ_[l]) (u ^ n - 1) =
      emultiplicity (l : ℤ_[l]) (u - 1) + emultiplicity l n := by
  have hu1 : (l : ℤ_[l]) ∣ u - 1 := (dvd_pow_self _ two_ne_zero).trans hu
  by_cases hl : l = 2
  · refine lte_reduce hu1 (fun k => ?_) n
    induction k with
    | zero => simp
    | succ k ih =>
      have hw : (l : ℤ_[l]) ^ 2 ∣ u ^ l ^ k - 1 := by
        have := sub_dvd_pow_sub_pow u 1 (l ^ k)
        rw [one_pow] at this
        exact hu.trans this
      rw [pow_succ, pow_mul, lte_two_step hl hw, ih]
      push_cast
      ring
  · exact emultiplicity_pow_sub_one_odd hl hu1 n

end KStar.TotallyRealRoots
