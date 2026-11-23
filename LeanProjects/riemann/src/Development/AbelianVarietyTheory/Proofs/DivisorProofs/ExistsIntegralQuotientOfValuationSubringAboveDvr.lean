import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

set_option autoImplicit false

noncomputable section

open Polynomial GlobalTheory.Published.AbVarRed IsLocalRing

namespace GlobalTheory.ValAbove

theorem partialSum_mul_pow_mem {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω] (c : ℕ → R) (n : ℕ)
    (x : Ω) (h : ∑ i ∈ Finset.range (n + 1), c i • x ^ i = 0) {m t : ℕ} (hm : m ≤ n) (ht : t ≤ n + 1) :
    (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t ∈
      Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n) := by
  have hmem : ∀ e, e ≤ n → ∀ r : R, r • x ^ e ∈
      Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n) := by
    intro e he r
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_image_of_mem _ (Set.mem_Iic.2 he)
  by_cases htm : t < m
  · rw [Finset.sum_mul]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [smul_mul_assoc, ← pow_add]
    exact hmem _ (by omega) _
  · push_neg at htm
    have hsplit := Finset.sum_range_add_sum_Ico (fun i => c i • x ^ i) (show m ≤ n + 1 by omega)
    rw [h] at hsplit
    have e1 : (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t
        = (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ i) * x ^ (t - m) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_Ico] at hi
      rw [smul_mul_assoc, smul_mul_assoc, ← pow_add, ← pow_add]
      congr 2
      omega
    have key : (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t
        = -∑ i ∈ Finset.range m, c i • x ^ (i + (t - m)) := by
      rw [e1, eq_neg_of_add_eq_zero_right hsplit, neg_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, ← pow_add]
    rw [key]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
    rw [Finset.mem_range] at hi
    exact hmem _ (by omega) _

theorem isIntegral_of_mul_pow_mem {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω] (n : ℕ) (x z : Ω)
    (hz : ∀ t ≤ n, z * x ^ t ∈
      Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n)) :
    IsIntegral R z := by
  refine isIntegral_of_smul_mem_submodule
    (Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n)) ?_ (Submodule.fg_span ((Set.finite_Iic n).image _)) z ?_
  · rw [Ne, Submodule.span_eq_bot]
    push_neg
    refine ⟨1, ?_, one_ne_zero⟩
    exact ⟨0, Set.mem_Iic.2 (Nat.zero_le n), pow_zero x⟩
  · intro w hw
    refine Submodule.span_induction (fun w hw => ?_) (by simp)
      (fun a b _ _ ha hb => by rw [smul_add]; exact Submodule.add_mem _ ha hb)
      (fun r a _ ha => by rw [smul_eq_mul, mul_smul_comm]; exact Submodule.smul_mem _ r ha) hw
    obtain ⟨t, ht, rfl⟩ := hw
    rw [Set.mem_Iic] at ht
    rw [smul_eq_mul]
    exact hz t (by omega)

theorem exists_integral_mul_eq_of_isAbove : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ y ∈ V, ∃ a s : Ω,
      ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem a ∧
      ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem s ∧ V.valuation s = 1 ∧ y * s = a := by
  intro R K Ω _ _ _ _ _ _ _ _ _ V hV y hy
  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hιinj : Function.Injective ((algebraMap K Ω).comp (algebraMap R K)) :=
    (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  have hmemV : ∀ r : R, algebraMap R Ω r ∈ V := by
    intro r
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨r, rfl⟩
    exact this
  have hle : ∀ r : R, V.valuation (algebraMap R Ω r) ≤ 1 := fun r => (V.valuation_le_one_iff _).2 (hmemV r)
  have hlt : ∀ r : R, ¬ IsUnit r → V.valuation (algebraMap R Ω r) < 1 := by
    intro r hr
    refine lt_of_le_of_ne (hle r) fun h1 => hr ?_
    have h0 : algebraMap R Ω r ≠ 0 := by
      intro h; rw [h, map_zero] at h1; exact zero_ne_one h1
    have hinv : (algebraMap R Ω r)⁻¹ ∈ V := (V.valuation_le_one_iff _).1 (by rw [map_inv₀, h1, inv_one])
    have hK : (algebraMap R K r)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω ((algebraMap R K r)⁻¹) ∈ V
      rw [map_inv₀]; exact hinv
    rw [hV] at hK
    obtain ⟨r', hr'⟩ := hK
    have hrK : algebraMap R K r ≠ 0 := by
      intro h; apply h0; change algebraMap K Ω (algebraMap R K r) = 0; rw [h, map_zero]
    have hrr : r * r' = 1 :=
      IsFractionRing.injective R K (by rw [map_mul, hr', mul_inv_cancel₀ hrK, map_one])
    exact ⟨⟨r, r', hrr, by rw [mul_comm, hrr]⟩, rfl⟩
  have hunit : ∀ r : R, IsUnit r → V.valuation (algebraMap R Ω r) = 1 := by
    intro r hr
    obtain ⟨u, rfl⟩ := hr
    have h := congrArg (fun w => V.valuation (algebraMap R Ω w)) u.mul_inv
    simp only [map_mul, map_one] at h
    refine le_antisymm (hle _) ?_
    by_contra hlt'
    push_neg at hlt'
    have : V.valuation (algebraMap R Ω ↑u) * V.valuation (algebraMap R Ω ↑u⁻¹) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' (hle _)) hlt'
    rw [h] at this
    exact lt_irrefl _ this

  classical
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have halgK : IsAlgebraic K y := Algebra.IsAlgebraic.isAlgebraic y
  have halgR : IsAlgebraic R y := (IsFractionRing.isAlgebraic_iff R K Ω).2 halgK
  obtain ⟨f, hf0, hfy⟩ := halgR
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hex : ∃ e : ℕ, ¬ (C (ϖ ^ (e + 1)) ∣ f) := by
    have hc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hf0
    obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    refine ⟨e, fun hd => ?_⟩
    have hd' : ϖ ^ e * ϖ ∣ ϖ ^ e * (u : R) := by
      rw [← pow_succ, mul_comm]; rw [← hu]
      exact (C_dvd_iff_dvd_coeff _ _).1 hd _
    have : ϖ ∣ (u : R) := (mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)).1 hd'
    exact hϖ.not_isUnit (isUnit_of_dvd_unit this u.isUnit)
  have hdiv : ∀ e, (∀ k < e, ¬ ¬ (C (ϖ ^ (k + 1)) ∣ f)) → C (ϖ ^ e) ∣ f := by
    intro e he
    cases e with
    | zero => simp
    | succ k => exact not_not.1 (he k (Nat.lt_succ_self k))
  obtain ⟨g, hg⟩ := hdiv (Nat.find hex) (fun k hk => Nat.find_min hex hk)
  have hgunit : ∃ i, IsUnit (g.coeff i) := by
    by_contra hno
    push_neg at hno
    apply Nat.find_spec hex
    have hmax : maximalIdeal R = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    have hCg : C ϖ ∣ g := (C_dvd_iff_dvd_coeff _ _).2 fun i => by
      have : g.coeff i ∈ maximalIdeal R := (mem_maximalIdeal _).2 (hno i)
      rw [hmax] at this
      exact Ideal.mem_span_singleton.1 this
    have h2 := mul_dvd_mul_left (C (ϖ ^ Nat.find hex)) hCg
    rw [← hg, ← C_mul, ← pow_succ] at h2
    exact h2
  have hgy : aeval y g = 0 := by
    rw [hg, map_mul, aeval_C] at hfy
    refine (mul_eq_zero.1 hfy).resolve_left ?_
    exact fun h => pow_ne_zero _ hϖ.ne_zero (hιinj (h.trans (map_zero _).symm))
  set n := g.natDegree with hn
  set c := g.coeff with hc
  have hsum : ∑ i ∈ Finset.range (n + 1), c i • y ^ i = 0 := by
    rw [← hgy, aeval_eq_sum_range]
  obtain ⟨i₀, hi₀⟩ := hgunit
  have hS : ((Finset.range (n + 1)).filter fun i => IsUnit (c i)).Nonempty :=
    ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (le_natDegree_of_ne_zero hi₀.ne_zero)), hi₀⟩⟩
  set j := ((Finset.range (n + 1)).filter fun i => IsUnit (c i)).max' hS with hj
  have hjmem := Finset.max'_mem _ hS
  rw [← hj, Finset.mem_filter, Finset.mem_range] at hjmem
  have hjn : j ≤ n := Nat.le_of_lt_succ hjmem.1
  have hbig : ∀ i, j < i → i ≤ n → ¬ IsUnit (c i) := by
    intro i hji hin hu
    have := Finset.le_max' ((Finset.range (n + 1)).filter fun i => IsUnit (c i)) i
      (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hu⟩)
    rw [← hj] at this
    omega
  set b := ∑ i ∈ Finset.Ico j (n + 1), c i • y ^ (i - j) with hb
  have hyle : V.valuation y ≤ 1 := (V.valuation_le_one_iff y).2 hy
  have hvb : V.valuation b = 1 := by
    rw [hb, Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hjn), Nat.sub_self, pow_zero, Algebra.smul_def,
      mul_one, add_comm]
    rw [Valuation.map_add_eq_of_lt_right, hunit _ hjmem.2]
    rw [hunit _ hjmem.2]
    refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [Algebra.smul_def, map_mul, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hyle _)) (hlt _ (hbig i (by omega) (by omega)))
  refine ⟨y * b, b, ?_, ?_, hvb, rfl⟩
  · exact isIntegral_of_mul_pow_mem n y (y * b) fun t ht => by
      rw [show y * b * y ^ t = b * y ^ (t + 1) by ring]
      exact partialSum_mul_pow_mem c n y hsum hjn (by omega)
  · exact isIntegral_of_mul_pow_mem n y b fun t ht => partialSum_mul_pow_mem c n y hsum hjn (by omega)

end GlobalTheory.ValAbove
