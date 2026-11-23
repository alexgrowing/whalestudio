import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuInf

namespace KStar.Tree

variable {Γ : Type} [Group Γ] (l : ℕ) [Fact l.Prime] (ε : Γ →* ℤ_[l]ˣ) (n : ℕ)

private theorem isUnit_of_not_dvd {c : ℤ_[l]} (hc : ¬ (l : ℤ_[l]) ∣ c) : IsUnit c := by
  rw [PadicInt.isUnit_iff]
  exact le_antisymm (PadicInt.norm_le_one c)
    (not_lt.1 fun h => hc ((PadicInt.norm_lt_one_iff_dvd c).1 h))

private theorem nuOf_mem (h : ∃ g, ε g ^ n ≠ 1) :
    ∃ g, ¬ (l : ℤ_[l]) ^ (nuOf l ε n + 1) ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by
  obtain ⟨g, hg⟩ := h
  have hx : ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h1
    apply hg
    ext
    simpa using h1
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  obtain ⟨u, v, hxv⟩ : ∃ (u : ℤ_[l]ˣ) (v : ℕ), ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 = u * (l : ℤ_[l]) ^ v :=
    ⟨_, _, PadicInt.unitCoeff_spec hx⟩
  have hne : {k | ∃ g, ¬ (l : ℤ_[l]) ^ (k + 1) ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1}.Nonempty := by
    refine ⟨v, g, ?_⟩
    intro hd
    rw [hxv, pow_succ, mul_comm (u : ℤ_[l])] at hd
    have hlu : (l : ℤ_[l]) ∣ u := (mul_dvd_mul_iff_left (pow_ne_zero v hl0)).1 hd
    have hlunit : IsUnit (l : ℤ_[l]) := isUnit_of_dvd_unit hlu u.isUnit
    have h1 := (PadicInt.norm_lt_one_iff_dvd (l : ℤ_[l])).2 dvd_rfl
    rw [PadicInt.isUnit_iff] at hlunit
    linarith
  exact Nat.sInf_mem hne

theorem pow_nuOf_dvd (g : Γ) : (l : ℤ_[l]) ^ nuOf l ε n ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by
  rcases Nat.eq_zero_or_pos (nuOf l ε n) with h0 | hpos
  · rw [h0, pow_zero]
    exact one_dvd _
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hlt : k < nuOf l ε n := by omega
    have hnm : k ∉ {k | ∃ g, ¬ (l : ℤ_[l]) ^ (k + 1) ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1} :=
      Nat.notMem_of_lt_sInf hlt
    rw [hk]
    by_contra hd
    exact hnm ⟨g, hd⟩

theorem exists_eq_pow_nuOf_mul_unit (h : ∃ g, ε g ^ n ≠ 1) :
    ∃ (g : Γ) (u : ℤ_[l]ˣ), ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 = (l : ℤ_[l]) ^ nuOf l ε n * u := by
  obtain ⟨g, hg⟩ := nuOf_mem l ε n h
  obtain ⟨c, hc⟩ := pow_nuOf_dvd l ε n g
  refine ⟨g, (isUnit_of_not_dvd l (c := c) ?_).unit, ?_⟩
  · rintro ⟨d, rfl⟩
    exact hg ⟨d, by rw [hc]; ring⟩
  · rw [IsUnit.unit_spec]
    exact hc

theorem le_nuOf_iff (h : ∃ g, ε g ^ n ≠ 1) (k : ℕ) :
    k ≤ nuOf l ε n ↔ ∀ g, (l : ℤ_[l]) ^ k ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by
  constructor
  · intro hk g
    exact (pow_dvd_pow _ hk).trans (pow_nuOf_dvd l ε n g)
  · intro hk
    by_contra hlt
    push_neg at hlt
    obtain ⟨g, hg⟩ := nuOf_mem l ε n h
    exact hg ((pow_dvd_pow _ hlt).trans (hk g))

theorem nuOf_pos_of_res (h : ∃ g, ε g ^ n ≠ 1) {K : Type} [CommRing K] [Nontrivial K] (θ : ℤ_[l] →+* K)
    (h1 : ∀ g, θ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n = 1) : 0 < nuOf l ε n := by
  have key := (le_nuOf_iff l ε n h 1).2 ?_
  · omega
  intro g
  rw [pow_one, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p]
  apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top θ)
  rw [RingHom.mem_ker, map_sub, map_pow, map_one, h1 g, sub_self]

end KStar.Tree
