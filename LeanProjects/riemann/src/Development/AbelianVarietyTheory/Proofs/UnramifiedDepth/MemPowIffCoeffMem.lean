import Mathlib

universe u_1 u_2

namespace GlobalTheory.IdealPowerCoefficients

open MvPowerSeries Finsupp

section SlopeTestRemainingChoices

variable {R : Type u_1} [CommRing R] {κ : Type u_2}

def coeffIdeal (I : Ideal R) (n : ℕ) : Ideal (MvPowerSeries κ R) where
  carrier := {f | ∀ e : κ →₀ ℕ, coeff e f ∈ I ^ (n - e.degree)}
  add_mem' := by
    intro f g hf hg e
    rw [map_add]
    exact Ideal.add_mem _ (hf e) (hg e)
  zero_mem' := by
    intro e
    simp
  smul_mem' := by
    intro c f hf e
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Ideal.sum_mem _ (fun p hp => ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right ?_ (hf p.2))
    have : e.degree = p.1.degree + p.2.degree := by rw [← hp, map_add]
    omega

theorem mem_coeffIdeal {I : Ideal R} {n : ℕ} {f : MvPowerSeries κ R} :
    f ∈ coeffIdeal I n ↔ ∀ e : κ →₀ ℕ, coeff e f ∈ I ^ (n - e.degree) := Iff.rfl

theorem coeffIdeal_mul_le (I : Ideal R) (a b : ℕ) :
    coeffIdeal (κ := κ) I a * coeffIdeal I b ≤ coeffIdeal I (a + b) := by
  classical
  rw [Ideal.mul_le]
  intro f hf g hg
  rw [mem_coeffIdeal] at hf hg ⊢
  intro e
  rw [coeff_mul]
  refine Ideal.sum_mem _ (fun p hp => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have h1 := Ideal.mul_mem_mul (hf p.1) (hg p.2)
  rw [← pow_add] at h1
  refine Ideal.pow_le_pow_right ?_ h1
  have : e.degree = p.1.degree + p.2.degree := by rw [← hp, map_add]
  omega

theorem le_coeffIdeal_one (I : Ideal R) :
    Ideal.map C I ⊔ Ideal.span (Set.range X) ≤ coeffIdeal (κ := κ) I 1 := by
  classical
  refine sup_le ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, mem_coeffIdeal]
    intro e
    rw [coeff_C]
    split_ifs with h
    · subst h
      simpa using hi
    · exact Ideal.zero_mem _
  · rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, mem_coeffIdeal]
    intro e
    rw [coeff_X]
    split_ifs with h
    · subst h
      simp
    · exact Ideal.zero_mem _

theorem pow_le_coeffIdeal (I : Ideal R) (n : ℕ) :
    (Ideal.map C I ⊔ Ideal.span (Set.range X)) ^ n ≤ coeffIdeal (κ := κ) I n := by
  induction n with
  | zero =>
    intro f _
    rw [mem_coeffIdeal]
    intro e
    simp
  | succ n ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih (le_coeffIdeal_one I)).trans (coeffIdeal_mul_le I n 1)

noncomputable def pick (d : κ →₀ ℕ) (k : κ) : κ :=
  if h : d.support.Nonempty then h.choose else k

theorem pick_eq (d : κ →₀ ℕ) (h : d ≠ 0) (k k' : κ) : pick d k = pick d k' := by
  have h' : d.support.Nonempty := Finsupp.support_nonempty_iff.2 h
  simp [pick, h']

theorem pick_mem (d : κ →₀ ℕ) (h : d ≠ 0) (k : κ) : pick d k ∈ d.support := by
  have h' : d.support.Nonempty := Finsupp.support_nonempty_iff.2 h
  rw [pick, dif_pos h']
  exact h'.choose_spec

noncomputable def cof [DecidableEq κ] (f : MvPowerSeries κ R) (k : κ) : MvPowerSeries κ R :=
  fun e => if pick (e + single k 1) k = k then coeff (e + single k 1) f else 0

theorem coeff_cof [DecidableEq κ] (f : MvPowerSeries κ R) (k : κ) (e : κ →₀ ℕ) :
    coeff e (cof f k) = if pick (e + single k 1) k = k then coeff (e + single k 1) f else 0 := by
  rw [coeff_apply]
  rfl

theorem decomp [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R) :
    f = C (coeff 0 f) + ∑ k, X k * cof f k := by
  classical
  ext d
  rw [map_add, map_sum, coeff_C]
  simp_rw [X, coeff_monomial_mul, one_mul, coeff_cof]
  by_cases hd : d = 0
  · subst hd
    simp [Finsupp.single_le_iff]
  · rw [if_neg hd, zero_add]
    obtain ⟨k0, -⟩ := Finsupp.support_nonempty_iff.2 hd
    have hterm : ∀ k, (if single k 1 ≤ d then
        (if pick (d - single k 1 + single k 1) k = k then coeff (d - single k 1 + single k 1) f
          else 0) else 0) = if pick d k0 = k then coeff d f else 0 := by
      intro k
      by_cases hk : single k 1 ≤ d
      · rw [if_pos hk, tsub_add_cancel_of_le hk, pick_eq d hd k k0]
      · rw [if_neg hk, if_neg]
        rintro rfl
        apply hk
        rw [Finsupp.single_le_iff]
        have := pick_mem d hd k0
        rw [Finsupp.mem_support_iff] at this
        omega
    rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_ite_eq]
    simp

theorem mem_pow_of_coeff [Finite κ] (I : Ideal R) (n : ℕ) (f : MvPowerSeries κ R)
    (hf : ∀ e : κ →₀ ℕ, coeff e f ∈ I ^ (n - e.degree)) :
    f ∈ (Ideal.map C I ⊔ Ideal.span (Set.range X)) ^ n := by
  classical
  have := Fintype.ofFinite κ
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [decomp f]
    refine Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun k _ => ?_)
    · have h0 := hf 0
      rw [map_zero, tsub_zero] at h0
      have h1 : C (coeff 0 f) ∈ Ideal.map (C : R →+* MvPowerSeries κ R) (I ^ (n + 1)) :=
        Ideal.mem_map_of_mem _ h0
      rw [Ideal.map_pow] at h1
      exact Ideal.pow_right_mono le_sup_left _ h1
    · rw [pow_succ']
      refine Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)) (ih _ fun e => ?_)
      rw [coeff_cof]
      split_ifs
      · have h2 := hf (e + single k 1)
        rw [map_add, degree_single] at h2
        have h3 : n + 1 - (e.degree + 1) = n - e.degree := by omega
        rwa [h3] at h2
      · exact Ideal.zero_mem _

end SlopeTestRemainingChoices

theorem mem_pow_iff_coeff_mem {R : Type u_1} [CommRing R] (I : Ideal R) {κ : Type u_2} [Finite κ] (n : ℕ)
    (f : MvPowerSeries κ R) :
    f ∈ (Ideal.map MvPowerSeries.C I ⊔ Ideal.span (Set.range MvPowerSeries.X)) ^ n ↔
      ∀ (e : κ →₀ ℕ), (MvPowerSeries.coeff e : MvPowerSeries κ R → R) f ∈
        I ^ (n - (Finsupp.degree : (κ →₀ ℕ) → ℕ) e) :=
  ⟨fun h => mem_coeffIdeal.1 (pow_le_coeffIdeal I n h), mem_pow_of_coeff I n f⟩

end GlobalTheory.IdealPowerCoefficients
