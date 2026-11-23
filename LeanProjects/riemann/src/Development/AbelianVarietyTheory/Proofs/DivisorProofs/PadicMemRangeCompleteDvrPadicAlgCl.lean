import Mathlib
open IsLocalRing

namespace GlobalTheory.PadicUnitBall

variable {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {κ : FractionRing V →+* PadicAlgCl p}

theorem norm_lt_one_of_mem_maximalIdeal
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)))
    {v : V} (hv : v ∈ maximalIdeal V) : ‖κ (algebraMap V (FractionRing V) v)‖ < 1 := by
  have hle : ‖κ (algebraMap V (FractionRing V) v)‖ ≤ 1 := (hV _).2 ⟨v, rfl⟩
  refine lt_of_le_of_ne hle fun h1 => ?_
  have hv0 : v ≠ 0 := by
    rintro rfl; simp at h1
  have hι : algebraMap V (FractionRing V) v ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hv0
  have hinv : ‖κ (algebraMap V (FractionRing V) v)⁻¹‖ ≤ 1 := by
    rw [map_inv₀, norm_inv, h1, inv_one]
  obtain ⟨w, hw⟩ := (hV _).1 hinv
  have hvw : v * w = 1 := by
    apply IsFractionRing.injective V (FractionRing V)
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hι]
  exact (mem_maximalIdeal _).1 hv ⟨⟨v, w, hvw, by rw [mul_comm]; exact hvw⟩, rfl⟩

theorem norm_natCast_p : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  have : ((p : ℕ) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by
    rw [map_natCast]
  rw [this, PadicAlgCl.norm_extends, Padic.norm_p]

theorem p_mem_maximalIdeal
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ((p : ℕ) : V) ∈ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have h1 : ‖κ (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖ ≤ 1 := (hV _).2 ⟨_, rfl⟩
  have h2 : κ (algebraMap V (FractionRing V) ((p : ℕ) : V)) *
      κ (algebraMap V (FractionRing V) (u⁻¹ : Vˣ)) = 1 := by
    rw [← map_mul, ← map_mul, ← hu, Units.mul_inv, map_one, map_one]
  have h3 := congrArg norm h2
  rw [norm_mul, norm_one, map_natCast, map_natCast, norm_natCast_p] at h3
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have : (p : ℝ)⁻¹ * ‖κ (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) h1) (inv_lt_one_of_one_lt₀ hp)
  linarith

end GlobalTheory.PadicUnitBall

namespace GlobalTheory.PadicUnitBall

variable {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {κ : FractionRing V →+* PadicAlgCl p}

theorem exists_norm_le_pow
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ n : ℕ, ∀ x ∈ maximalIdeal V ^ n,
      ‖κ (algebraMap V (FractionRing V) x)‖ ≤ r ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hmax := hϖ.maximalIdeal_eq
  refine ⟨‖κ (algebraMap V (FractionRing V) ϖ)‖, norm_nonneg _,
    norm_lt_one_of_mem_maximalIdeal hV (by rw [hmax]; exact Ideal.mem_span_singleton_self ϖ),
    fun n x hx => ?_⟩
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨w, rfl⟩ := hx
  rw [map_mul, map_mul, norm_mul, map_pow, map_pow, norm_pow]
  have hw : ‖κ (algebraMap V (FractionRing V) w)‖ ≤ 1 := (hV _).2 ⟨w, rfl⟩
  exact mul_le_of_le_one_right (by positivity) hw

theorem smul_top_eq (I : Ideal V) : (I • ⊤ : Submodule V V) = I := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem padicInt_mem_range
    (hc : IsAdicComplete (maximalIdeal V) V)
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) (z : ℤ_[p]) :
    ∃ L : V, κ (algebraMap V (FractionRing V) L) = algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p]) := by
  set f : ℕ → V := fun n => ((z.appr n : ℕ) : V) with hf
  have hpm := p_mem_maximalIdeal hV
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (maximalIdeal V) ^ m • (⊤ : Submodule V V)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_top_eq]
    obtain ⟨c, hc⟩ := PadicInt.dvd_appr_sub_appr z m n hmn
    have hmono : z.appr m ≤ z.appr n := PadicInt.appr_mono z hmn
    have heq : z.appr n = z.appr m + p ^ m * c := by
      generalize p ^ m * c = k at hc; omega
    have : f m - f n = ((p : ℕ) : V) ^ m * (-(c : V)) := by
      simp only [hf, heq]; push_cast; ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpm m)
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec hcauchy
  refine ⟨L, ?_⟩
  obtain ⟨r, hr0, hr1, hr⟩ := exists_norm_le_pow hV
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hbound : ∀ n : ℕ, ‖κ (algebraMap V (FractionRing V) L) - algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p])‖
      ≤ r ^ n + ((p : ℝ)⁻¹) ^ n := by
    intro n
    have h1 : f n - L ∈ maximalIdeal V ^ n := by
      have := hL n
      rwa [SModEq.sub_mem, smul_top_eq] at this
    have h1' := hr n _ h1
    have hfn : κ (algebraMap V (FractionRing V) (f n)) =
        algebraMap ℚ_[p] (PadicAlgCl p) (((z.appr n : ℕ) : ℤ_[p]) : ℚ_[p]) := by
      simp only [hf, map_natCast, PadicInt.coe_natCast]
    have h2 : ‖z - ((z.appr n : ℕ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow _ n).2 (PadicInt.appr_spec n z)
    rw [zpow_neg, zpow_natCast, ← inv_pow] at h2
    have h2' : ‖algebraMap ℚ_[p] (PadicAlgCl p) (((z.appr n : ℕ) : ℤ_[p]) : ℚ_[p]) -
        algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p])‖ ≤ ((p : ℝ)⁻¹) ^ n := by
      rw [← map_sub, PadicAlgCl.norm_extends, ← PadicInt.coe_sub, PadicInt.norm_def.symm, norm_sub_rev]
      exact h2
    calc _ = ‖(κ (algebraMap V (FractionRing V) L) - κ (algebraMap V (FractionRing V) (f n))) +
          (κ (algebraMap V (FractionRing V) (f n)) - algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p]))‖ := by
            congr 1; ring
      _ ≤ _ := norm_add_le _ _
      _ ≤ r ^ n + ((p : ℝ)⁻¹) ^ n := by
        gcongr
        · rw [norm_sub_rev, ← map_sub, ← map_sub]; exact h1'
        · rw [hfn]; exact h2'
  have ht : Filter.Tendsto (fun n : ℕ => r ^ n + ((p : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp))
    simpa using this
  have h0 := ge_of_tendsto' ht hbound
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

end GlobalTheory.PadicUnitBall

namespace GlobalTheory.PadicUnitBall

theorem padic_mem_range : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V →
    ∀ (κ : FractionRing V →+* PadicAlgCl p),
    (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) →
    ∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range := by
  intro p _ V _ _ _ _ hc κ hV q
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖q‖ hp
  have hz : ‖q * (p : ℚ_[p]) ^ k‖ ≤ 1 := by
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    rw [mul_inv_le_iff₀ (by positivity), one_mul]
    exact hk.le
  obtain ⟨L, hL⟩ := padicInt_mem_range hc hV (⟨q * (p : ℚ_[p]) ^ k, hz⟩ : ℤ_[p])
  have hpne : ((p : ℕ) : PadicAlgCl p) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨algebraMap V (FractionRing V) L * (((p : ℕ) : FractionRing V) ^ k)⁻¹, ?_⟩
  rw [map_mul, hL, map_inv₀, map_pow, map_natCast]
  show algebraMap ℚ_[p] (PadicAlgCl p) (q * (p : ℚ_[p]) ^ k) * _ = _
  simp only [map_mul, map_pow, map_natCast]
  field_simp

end GlobalTheory.PadicUnitBall
