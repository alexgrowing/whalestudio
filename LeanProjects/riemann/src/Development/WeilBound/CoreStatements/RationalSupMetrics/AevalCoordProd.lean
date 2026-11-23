import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier

set_option linter.unusedSectionVars false

namespace MultiProjectiveCoordinates.Val

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mh_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem mh_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem mh_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm k

theorem mh_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  exact mh_add hf (mh_neg hg)

theorem mh_C (r : ℤ) : IsMultiHomog (C r : MRing ι) 0 := by
  classical
  intro m hm k
  have h0 : m = 0 := by
    by_contra h
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C, if_neg (Ne.symm h)] at hm
    exact hm rfl
  subst h0
  simp

theorem mh_one : IsMultiHomog (1 : MRing ι) 0 := by
  have := mh_C (ι := ι) 1
  rwa [map_one] at this

theorem mh_X [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, this, h]

theorem mh_pow {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact mh_one
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact mh_mul ih hf

theorem mh_coordProd (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ d k)
      (∑ k ∈ s, d k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact mh_one
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact mh_mul (mh_pow (mh_X k (c k)) _) ih
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [e] at this

theorem map_aeval_int {σ R S : Type*} [CommRing R] [Algebra ℤ R] [CommRing S] [Algebra ℤ S]
    (φ : R →+* S) (z : σ → R) (f : MvPolynomial σ ℤ) :
    φ (aeval z f) = aeval (fun p => φ (z p)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [aeval_C, aeval_C, eq_intCast (algebraMap ℤ R), eq_intCast (algebraMap ℤ S), map_intCast]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, aeval_X]

theorem aeval_scale {R : Type*} [CommRing R] [Algebra ℤ R] (z : (Σ k, ι k) → R) (t : K → R)
    {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval (fun p : Σ k, ι k => z p * t p.1) g = aeval z g * ∏ k, t k ^ d k := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_assoc]
  congr 1
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← hg m hm k, ← Finset.prod_pow_eq_pow_sum]

variable {Ω : Type} [Field Ω]

theorem mem_of_form (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
  have h := aeval_scale (fun p => (C (y p) : MvPolynomial K Ω)) (fun k => X k) hg
  rw [← map_aeval_int (C : Ω →+* MvPolynomial K Ω) y g, h0, map_zero, zero_mul] at h
  exact h

theorem form_vanish (y : (Σ k, ι k) → Ω) {𝕜 : Type} [Field 𝕜] {z : (Σ k, ι k) → 𝕜}
    (hz : z ∈ ptsOver 𝕜 (mCoordIdeal y)) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (h0 : aeval y g = 0) : aeval z g = 0 :=
  hz.2 g (mem_of_form y hg h0)

theorem aeval_coordProd (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) = ∏ k, y ⟨k, c k⟩ ^ d k := by
  simp only [map_prod, map_pow, aeval_X]

theorem homog (c : ∀ k, ι k) (f : MRing ι) : ∃ d₀ : K → ℕ, ∀ d : K → ℕ, d₀ ≤ d →
    ∃ g : MRing ι, IsMultiHomog g d ∧ ∀ (𝕜 : Type) [Field 𝕜] (z : (Σ k, ι k) → 𝕜),
      (∀ k, z ⟨k, c k⟩ ≠ 0) →
      aeval (fun p : Σ k, ι k => z p / z ⟨p.1, c p.1⟩) f * ∏ k, z ⟨k, c k⟩ ^ d k = aeval z g := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, fun d _ => ⟨C a * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k, ?_, fun 𝕜 _ z _ => ?_⟩⟩
    · have := mh_mul (mh_C (ι := ι) a) (mh_coordProd c d)
      rwa [zero_add] at this
    · rw [map_mul, aeval_coordProd, aeval_C, aeval_C]
  | add p q hp hq =>
    obtain ⟨d1, h1⟩ := hp
    obtain ⟨d2, h2⟩ := hq
    refine ⟨d1 ⊔ d2, fun d hd => ?_⟩
    obtain ⟨g1, hg1, e1⟩ := h1 d (le_sup_left.trans hd)
    obtain ⟨g2, hg2, e2⟩ := h2 d (le_sup_right.trans hd)
    refine ⟨g1 + g2, mh_add hg1 hg2, fun 𝕜 _ z hz => ?_⟩
    rw [map_add, map_add, add_mul, e1 𝕜 z hz, e2 𝕜 z hz]
  | mul_X p n hp =>
    obtain ⟨d1, h1⟩ := hp
    obtain ⟨k0, i0⟩ := n
    refine ⟨d1 + Pi.single k0 1, fun d hd => ?_⟩
    obtain ⟨d', rfl⟩ : ∃ d' : K → ℕ, d = d' + Pi.single k0 1 :=
      ⟨d - Pi.single k0 1, (tsub_add_cancel_of_le (le_add_self.trans hd)).symm⟩
    obtain ⟨g1, hg1, e1⟩ := h1 d' (le_of_add_le_add_right hd)
    have hX : IsMultiHomog (X ⟨k0, i0⟩ : MRing ι) (Pi.single k0 1) := mh_X k0 i0
    refine ⟨_, mh_mul hg1 hX, fun 𝕜 _ z hz => ?_⟩
    have e : ∏ k, z ⟨k, c k⟩ ^ (d' + Pi.single k0 1 : K → ℕ) k =
        (∏ k, z ⟨k, c k⟩ ^ d' k) * z ⟨k0, c k0⟩ := by
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_single k0]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    rw [map_mul, map_mul, aeval_X, aeval_X, e, ← e1 𝕜 z hz]
    have := hz k0
    field_simp

end MultiProjectiveCoordinates.Val
