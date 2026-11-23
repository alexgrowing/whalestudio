import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingMemCoefficientField
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.TameCoupledEx

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem val_g_lt (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (hA : IsPlaceOver (F := E) A v) {g : ℕ}
    (hg : ((g : ℕ) : 𝓞 E) ∈ v.asIdeal) : A.valuation ((g : ℕ) : Ω) < 1 := by
  have := (hA ((g : ℕ) : 𝓞 E)).2 hg
  simpa using this

omit [NumberField E] in

theorem val_nat_not_lt (A : ValuationSubring Ω) {g m : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    (hm : ¬ g ∣ m) : ¬ A.valuation ((m : ℕ) : Ω) < 1 := by
  intro hm1
  obtain ⟨a, b, hab⟩ : IsCoprime (m : ℤ) (g : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hgp).2 hm))
  have hle : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A z)
  have e : (a : Ω) * m + (b : Ω) * g = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have : A.valuation ((a : Ω) * m + (b : Ω) * g) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hle a) zero_le hm1
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hle b) zero_le hg
  rw [e, map_one] at this
  exact lt_irrefl _ this

theorem fix_rou {A : ValuationSubring Ω} {g : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {m : ℕ} (hm : 0 < m) (hgm : ¬ g ∣ m) {μ : Ω} (hμ : μ ^ m = 1) :
    σ μ = μ := by
  refine ReciprocityTheory.Gal.eq_of_pow_eq_one A (val_nat_not_lt A hgp hg hgm) (by rw [← map_pow, hμ, map_one]) hμ ?_
  exact hσ.2 μ ((A.valuation_le_one_iff _).2 (Formalism.L2.NT.mem_of_pow_eq_one A hm hμ))

theorem not_dvd_pow_sub_one {g d : ℕ} (hgp : g.Prime) (hd : 0 < d) : ¬ g ∣ g ^ d - 1 := by
  intro h
  have h1 : g ∣ g ^ d := dvd_pow_self g hd.ne'
  have h2 : 1 < g ^ d := Nat.one_lt_pow hd.ne' hgp.one_lt
  have h3 : g ∣ g ^ d - (g ^ d - 1) := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self h2.le] at h3
  exact hgp.not_dvd_one h3

theorem pow_sub_one_pos {g d : ℕ} (hgp : g.Prime) (hd : 0 < d) : 0 < g ^ d - 1 := by
  have h2 : 1 < g ^ d := Nat.one_lt_pow hd.ne' hgp.one_lt
  omega

variable [CharZero Ω]

omit [NumberField E] in
theorem ne_zero_of_pow_eq {g N : ℕ} (hgp : g.Prime) (hN : 0 < N) {y : Ω} (hy : y ^ N = ((g : ℕ) : Ω)) : y ≠ 0 := by
  rintro rfl
  rw [zero_pow hN.ne'] at hy
  exact (Nat.cast_ne_zero.2 hgp.ne_zero : ((g : ℕ) : Ω) ≠ 0) hy.symm

theorem ratio_indep {A : ValuationSubring Ω} {g : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {N : ℕ} (hN : 0 < N) (hgN : ¬ g ∣ N) {y y' : Ω}
    (hy : y ^ N = ((g : ℕ) : Ω)) (hy' : y' ^ N = ((g : ℕ) : Ω)) : σ y' / y' = σ y / y := by
  have hg0 : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hgp.ne_zero
  have hy0 := ne_zero_of_pow_eq hgp hN hy
  obtain ⟨μ, rfl⟩ : ∃ μ, y' = μ * y := ⟨y' / y, by field_simp⟩
  have hμ : μ ^ N = 1 := by
    rw [mul_pow, hy] at hy'
    exact (mul_eq_right₀ hg0).1 hy'
  have hμ0 : μ ≠ 0 := by rintro rfl; rw [zero_pow hN.ne'] at hμ; exact zero_ne_one hμ
  rw [map_mul, fix_rou hgp hg hσ hN hgN hμ]
  field_simp

theorem ratio_mul {A : ValuationSubring Ω} {g : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (τ : G E Ω) {N : ℕ} (hN : 0 < N) (hgN : ¬ g ∣ N) {y : Ω}
    (hy : y ^ N = ((g : ℕ) : Ω)) : (σ * τ) y / y = (σ y / y) * (τ y / y) := by
  have hg0 : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hgp.ne_zero
  have hy0 := ne_zero_of_pow_eq hgp hN hy
  have hc : (τ y / y) ^ N = 1 := tameQuot_pow τ hg0 hy
  set c := τ y / y with hcdef
  have e : τ y = c * y := by rw [hcdef]; field_simp
  rw [AlgEquiv.mul_apply, e, map_mul, fix_rou hgp hg hσ hN hgN hc]
  field_simp

theorem ratio_pow {A : ValuationSubring Ω} {g : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {N : ℕ} (hN : 0 < N) (hgN : ¬ g ∣ N) {y : Ω}
    (hy : y ^ N = ((g : ℕ) : Ω)) (j : ℕ) : (σ ^ j) y / y = (σ y / y) ^ j := by
  have hy0 := ne_zero_of_pow_eq hgp hN hy
  induction j with
  | zero => simp [hy0]
  | succ j ih =>
    rw [pow_succ, ratio_mul hgp hg (pow_mem hσ j) σ hN hgN hy, ih, pow_succ]

theorem root_down {g d D : ℕ} (hdD : d ∣ D) {r : Ω} (hr : r ^ (g ^ D - 1) = ((g : ℕ) : Ω)) :
    (r ^ ((g ^ D - 1) / (g ^ d - 1))) ^ (g ^ d - 1) = ((g : ℕ) : Ω) := by
  rw [← pow_mul, Nat.div_mul_cancel (Nat.pow_sub_one_dvd_pow_sub_one g hdD), hr]

theorem ratio_descent {A : ValuationSubring Ω} {g : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {d D : ℕ} (hd : 0 < d) (hdD : d ∣ D) {y r : Ω}
    (hy : y ^ (g ^ d - 1) = ((g : ℕ) : Ω)) (hr : r ^ (g ^ D - 1) = ((g : ℕ) : Ω)) :
    σ y / y = (σ r / r) ^ ((g ^ D - 1) / (g ^ d - 1)) := by
  rw [ratio_indep hgp hg hσ (pow_sub_one_pos hgp hd) (not_dvd_pow_sub_one hgp hd) (root_down hdD hr) hy,
    map_pow, div_pow]

end

theorem val_sub_one_lt_of_red {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {l : ℕ} [Fact l.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar l) {x : Ω} (hx : x ∈ A) (h : redThrough A κ x = 1) :
    A.valuation (x - 1) < 1 := by
  unfold redThrough at h
  rw [dif_pos hx] at h
  have h1 : IsLocalRing.residue A ⟨x, hx⟩ = IsLocalRing.residue A 1 := κ.injective (by rw [h, map_one, map_one])
  have h2 : (⟨x, hx⟩ : A) - 1 ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq.1 h1
  have h3 := (A.valuation_lt_one_iff _).1 h2
  simpa using h3

end GlobalTheory.TameCoupledEx
